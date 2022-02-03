open Core_kernel
open Syntax
open Formula
open HeapType
open Result
open Let_syntax
module Log = (val Logs.src_log Logging.substitution_src : Logs.LOG)

module FormulaId = struct
  module T = struct
    type t =
      | Invalid of Instance.t
      | Valid of Instance.t
      | InstEqual of Instance.t
      | EqBv of Expression.t
      | EqInst of Instance.t
      | EqBvSl of (Sliceable.t * int * int)
      | EqArith of Expression.t
      | EqVal of Expression.t
      | Err of string
      [@@deriving compare, sexp] 
  end
  include T
  include Comparable.Make(T)
end

type fid_map =
  Formula.t Map.M(FormulaId).t
[@@deriving sexp]
let pp_fromula_id (pp : Format.formatter) (fid :FormulaId.t) = 
  let open Fmt in
  match fid with
    | Invalid i -> pf pp "invalid_%s" i.name
    | Valid i -> pf pp "valid_%s" i.name
    | InstEqual i -> pf pp "inst_equal_%s" i.name
    | EqBv e -> pf pp "eq_bv_%a" Pretty.pp_expr_raw e
    | EqBvSl (i, s, e) -> pf pp "eq_bv_sl_%a[%i:%i]" Pretty.pp_sliceable_raw i s e
    | EqInst i -> pf pp "eq_inst_%s" i.name
    | EqArith e -> pf pp "eq_arith_%a" Pretty.pp_expr_raw e
    | EqVal e -> pf pp "eq_val_%a" Pretty.pp_expr_raw e
    | Err e -> pf pp "Error: %s" e


let merge_map (map1 : (FormulaId.t , 'b, 'c) Map.t) (map2 : (FormulaId.t, 'b, 'c) Map.t) =
  let combine ~(key : FormulaId.t ) (v1 : 'b) (_ : 'b) : 'b =
    let _ = key in
    v1
  in
  Map.merge_skewed  map1 map2 ~combine:combine

let rec get_subs_expr exp : (Expression.t option) =
  let open Expression in
  match exp with
  | ArithExpr (Plus (a1, a2)) -> (
    let opt1 = get_subs_expr (ArithExpr a1) in
    match opt1 with
    | Some _ -> opt1
    | None ->  get_subs_expr (ArithExpr a2))
  | ArithExpr (Length (_)) ->  Some exp
  | ArithExpr (Num (_)) ->  None
  | BvExpr (Concat (b1, b2)) -> (
    let opt1 = get_subs_expr (BvExpr b1) in
    let opt2 = get_subs_expr (BvExpr b2) in
    match (opt1, opt2) with
      | Some BvExpr Packet _, Some BvExpr Slice _ -> opt1
      | Some BvExpr Packet _, Some BvExpr Packet _
      | Some BvExpr Slice _, Some BvExpr Packet _ -> opt2
      | Some _ , None ->  opt1
      | None , Some _ -> opt2
      | _ -> None)
  | BvExpr (Slice (_)) -> Some exp
  | BvExpr (Packet (_)) -> Some exp
  | BvExpr (Minus (_))
  | BvExpr (Bv (_)) -> None

let replace_expression exp_i exp_o exp_r =
  let open Expression in
  if [%compare.equal: Expression.t ] exp_i exp_o then Ok exp_r
  else
  let rec replace_arith exp_i exp_o exp_r : Expression.arith = 
    let open Expression in
    if [%compare.equal: Expression.arith ] exp_i exp_o then exp_r
    else
    match exp_i with
    | Plus (a1, a2) -> Plus(replace_arith a1 exp_o exp_r, replace_arith a2 exp_o exp_r)
    | Length (_)
    | Num (_) ->  exp_i
  in
  let rec replace_bv exp_i exp_o exp_r : Expression.bv = 
    let open Expression in
    if [%compare.equal: Expression.bv ] exp_i exp_o then exp_r
    else
    match exp_i with
    | Concat (b1, b2) -> Concat(replace_bv b1 exp_o exp_r, replace_bv b2 exp_o exp_r)
    | Minus (b1, b2) -> Minus(replace_bv b1 exp_o exp_r, replace_bv b2 exp_o exp_r)
    | Slice (_)
    | Packet (_)
    | Bv (_) -> exp_i
  in
  match exp_i, exp_o, exp_r with
  | ArithExpr exp1, ArithExpr exp2, ArithExpr exp3 -> Ok (ArithExpr(replace_arith exp1 exp2 exp3))
  | BvExpr exp1, BvExpr exp2, BvExpr exp3 -> Ok (BvExpr(replace_bv exp1 exp2 exp3))
  | _ -> Error(Error.of_string "All arguments must be of type ArithExpr or BvExpr")


let extract_to_map form : (FormulaId.t, Formula.t , FormulaId.comparator_witness) Map.t=
  let rec ext (f : Formula.t) 
    (m_in : (FormulaId.t, Formula.t , FormulaId.comparator_witness) Map.t ) 
    : (FormulaId.t, Formula.t , FormulaId.comparator_witness) Map.t =
    match f with
    | And(f1, f2) -> 
      let m_tmp1 = ext f1 m_in in
      ext f2 m_tmp1
    | Or(And(Neg(IsValid(v1, i1)),Neg(IsValid(v2,i2))), And(And(IsValid(v3,i3),IsValid(v4,i4)), Eq (BvExpr(_), BvExpr(_)))) -> 
      if phys_equal v1 v3 && phys_equal v2 v4 && phys_equal i1 i2  && phys_equal i3 i4  && phys_equal i2 i3
        then (
          let k = FormulaId.InstEqual i1 in
          Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw  f);
          Map.set m_in ~key:k ~data:f
        )
        else (
          Log.debug (fun m -> m "@[Suspicious Or-Expression: this should not happen @]");
          Map.set m_in ~key:(Err "Suspicious Or-Expression") ~data:f
        )
    | True -> m_in
    | Eq (exp1, _) 
    | Gt (exp1, _) -> (
      let opt = get_subs_expr exp1 in 
      match opt with
      | Some o -> (
        match o with 
        | BvExpr(Slice(inst, s, e)) -> 
          let k = FormulaId.EqBvSl (inst, s, e ) in
          let m_tmp = match inst with
          | Instance(_, inst) -> 
            let k_i = FormulaId.EqInst inst in
            Log.debug (fun m -> m "@[Searching for %a@]" pp_fromula_id k_i);
            let inst_opt = Map.find m_in k_i in
            (* Log.debug (fun m -> m "@[Searching in: %s@]" (Sexp.to_string_hum (sexp_of_fid_map  m_in))); *)
            let data = match inst_opt with
            | Some inst -> 
              Log.debug (fun m -> m "@[Found %a@]" Pretty.pp_form_raw inst);
              And(inst, f)
            | None -> 
              Log.debug (fun m -> m "@[Nothing found@]");
              f
            in
            Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k_i Pretty.pp_form_raw  data);
            let m_t = Map.set m_in ~key:k_i ~data:data in
            (* Log.debug (fun m -> m "@[Retruning: %s@]" (Sexp.to_string_hum (sexp_of_fid_map  m_t))); *)
            m_t
          | _ -> m_in
          in
          Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw  f);
          Map.set m_tmp ~key:k ~data:f
        | BvExpr _ ->  
          let k = FormulaId.EqBv o in
          Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw  f);
          Map.set m_in ~key:k ~data:f
        | ArithExpr _ ->  
          let k = FormulaId.EqArith o in
          Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw  f);
          Map.set m_in ~key:k ~data:f)
      | None -> m_in)
    | Neg(IsValid(_,i)) -> 
      let k = FormulaId.Invalid i in
      Log.debug(fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw f);
      Map.set m_in ~key:k ~data:f
    | IsValid(_, i) -> 
      let k = FormulaId.Valid i in
      Log.debug(fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw f);
      Map.set m_in ~key:k ~data:f
    | _ -> 
      Log.debug(fun m -> m "@[Unmatched Form: %a@]" Pretty.pp_form_raw f);
      m_in
  in
  let map = Map.empty(module FormulaId) in
  ext form map

let rec append_slices form lst : Formula.t =
  match lst with
  | (key, vl)::t ->( 
    let open FormulaId in
    match (key, vl) with 
    | (EqBvSl _, vl) -> And(vl, append_slices form t)
    | _ -> append_slices form t)
  | [] -> form

let shift_slice_var v_new sl =
  let open Sliceable in
  match sl with
  | Instance (_, p) -> Instance (v_new, p)
  | Packet (_, p) -> Packet (v_new, p)

let shift_exp_var v_new exp : Expression.t = 
  let open Expression in
  let rec shift_arith v_new arith =
    match arith with
    | Length(_, p) -> Length(v_new, p)
    | Plus(a1, a2) -> Plus(shift_arith v_new a1, shift_arith v_new a2)
    | Num _ ->  arith
  in
  let rec shift_bv v_new bv =
    match bv with
    | Minus (b1, b2) -> Minus(shift_bv v_new b1, shift_bv v_new b2)
    | Bv _ -> bv
    | Concat (b1, b2) -> Concat(shift_bv v_new b1, shift_bv v_new b2)
    | Slice (s, hi, lo) -> Slice(shift_slice_var v_new s, hi, lo)
    | Packet (_, p) -> Packet(v_new, p)
  in
  match exp with
  | ArithExpr arith -> ArithExpr(shift_arith v_new arith)
  | BvExpr bv -> BvExpr(shift_bv v_new bv)


let rec simplify_formula (form : Formula.t) (map : (FormulaId.t , Formula.t , FormulaId.comparator_witness) Map.t) : Formula.t =
    let result = 
      match form with
      | And(f1, f2) -> Ok (And(simplify_formula f1 map, simplify_formula  f2 map))
      | Or(And(Neg(IsValid(v1, i1)),Neg(IsValid(_))), And(IsValid(_),IsValid(_))) -> 
        let smpl = IsValid(v1, i1) in
        Log.debug (fun m -> m "@[replaced @ %a @ by@ %a@]" Pretty.pp_form_raw form Pretty.pp_form_raw smpl);
        Ok smpl
      (* Simplification --> Replace by recursive fun for f1, f2 *)
      | Or(And(Neg(IsValid(v1, i1)),Neg(IsValid(_))), And(And(IsValid(_),IsValid(_)), And(f1, f2))) -> (
        let valid_result = Map.find map (Valid i1) in
        match valid_result with
        | Some _ -> (
          let smpl = IsValid(v1, i1) in
          Log.debug (fun m -> m "@[replaced @ %a @ by@ %a@]" Pretty.pp_form_raw form Pretty.pp_form_raw smpl);
          Ok (And(smpl, And(f1,f2))))
        | None -> Ok form)
      | Or(And(Neg(IsValid(v1, i1)),Neg(IsValid(v2, i2))), And(And(IsValid(v3, i3),IsValid(v4, i4)), Eq (_, _))) -> (
        let k = (FormulaId.EqInst i1) in
        let valid_result = Map.find map (Valid i1) in
        Log.debug (fun m -> m "@[searching for %a@]" pp_fromula_id k);
        let slice_result = Map.find_or_error map k  in
        match valid_result with
        | Some _ -> (
          let smpl = IsValid(v1, i1) in
          Log.debug (fun m -> m "@[replaced @ %a @ by@ %a@]" Pretty.pp_form_raw form Pretty.pp_form_raw smpl);
          match slice_result with
          | Ok sl -> 
            Log.debug (fun m -> m "@[appended @ %a@]" Pretty.pp_form_raw sl);
            Ok (And(smpl, sl))
          | _ -> Ok smpl)
        | None -> (
          match slice_result with
          | Ok sl -> 
            Log.debug (fun m -> m "@[appended @ %a@]" Pretty.pp_form_raw sl);
            Ok (Or(And(Neg(IsValid(v1, i1)),Neg(IsValid(v2, i2))), And(And(IsValid(v3, i3), IsValid(v4, i4)), sl)))
          | _ -> Ok form))
      | Eq (exp1 , exp2) -> 
        let%bind subsId = match exp2 with
        | ArithExpr Length (_, pkt) -> Ok (FormulaId.EqArith (ArithExpr (Length(0, pkt))))
        | BvExpr Bv _ -> Ok (EqVal exp2) (*nonsense!?*)
        | BvExpr Slice (s, h, t) -> (
          let open Sliceable in
          match s with
          | Packet (_,p) -> Ok (EqBv (BvExpr (Slice (Packet (0,p), h, t))))
          | Instance (_, i) -> Ok (EqBv (BvExpr (Slice (Instance (0,i), h, t)))))
        | BvExpr Packet (_, p) -> Ok (EqBv (BvExpr (Packet (0,p))))
        | _ -> Error (Error.of_string "Nothing to replace")
        in
        let%bind subs = Map.find_or_error map subsId
        in
        let%bind substitution_l = 
          match subs with
          | Eq (subs_l, _)
          | Gt (subs_l, _) -> Ok subs_l
          | _ -> Error (Error.of_string "Nothing to replace")
        in  
        let%bind substitution_r = 
          match subs with
          | Eq (_ , subs_r)
          | Gt (_, subs_r) -> Ok subs_r
          | _ -> Error (Error.of_string "Nothing to replace")
        in
        let%bind exp_old = 
          match subsId with
          | EqBv exp
          | EqArith exp
          | EqVal exp -> Ok exp
          | _ -> Error (Error.of_string "Unexpected FormulaId")
        in
        Log.debug (fun m -> m "@[replaced @ %a @ by@ %a@ in %a@]" 
          Pretty.pp_expr_raw exp_old 
          Pretty.pp_expr_raw exp1 
          Pretty.pp_expr_raw substitution_l);
        let%bind exp_new = replace_expression substitution_l exp_old exp1
        in
        Ok (Eq(exp_new, substitution_r))
      | _ -> Ok form
    in 
    match result with 
    | Ok f -> f
    | _ -> form


let rec simplify (hty : HeapType.t) : HeapType.t =
  let hty = Simplify.fold_refinements hty in
  let result = (
    match hty with
    | Substitution (h, _, subs) -> (
      let h = simplify h in
      let subs = simplify subs in
      let%bind subs_map = 
        match subs with
        | Refinement(_,_,f_subs) -> Ok (extract_to_map f_subs)
        | _ ->  Error (Error.of_string "subs is not a Refinement")
      in
      match h with
      |Refinement(s,ht,f) -> (
        Ok (Refinement(s, ht, simplify_formula f subs_map))
      )
      |Choice(Refinement(s1,ht1,f1), Refinement(s2,ht2,f2)) -> (
        Ok (Choice(Refinement(s1, ht1, simplify_formula f1 subs_map), Refinement(s2, ht2, simplify_formula f2 subs_map)))
      )
      | _ ->  Error (Error.of_string "h is not a Refinement"))   
    | _ -> Error (Error.of_string "hty is not a substitution"))
  in
  match result with
  | Ok ht -> 
    Log.debug (fun m -> m "@[Simplifying %a@]" Pretty.pp_header_type_raw hty);
    Log.debug (fun m -> m "@[Resulting hty %a@]" Pretty.pp_header_type_raw ht);
    ht
  | _ -> hty 
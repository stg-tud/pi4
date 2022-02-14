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
      | Valid of int * Instance.t * bool                      (* x.τ.valid *)
      | InstEqual of int * Instance.t                   (* x.τ == y.τ *)
      | ValidEqual of int * Instance.t                  (* x.τ.valid == y.τ.valid *)
      | EqExp of Expression.t                           (* x.exp == y.exp *)
      | GtExp of Expression.t                           (* x.exp > y.exp *)
      | EqInst of int * Instance.t                      (* x.τ == y.exp_bv *)
      | EqBvSl of (Sliceable.t * int * int)             (* x.τ[hi:lo] == y.exp_bv *)
      | EqBv of Expression.t                            (* x.τ == y.bv *)
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
    | Valid (v, i, b) -> pf pp "valid_%b_%i.%s" b v i.name
    | InstEqual (v, i) -> pf pp "inst_equal_%i.%s" v i.name
    | ValidEqual (v, i) ->  pf pp "valid_equal_%i.%s" v i.name
    | GtExp e -> pf pp "gt_exp_%a" Pretty.pp_expr_raw e
    | EqExp e -> pf pp "eq_exp_%a" Pretty.pp_expr_raw e
    | EqInst (v, i) -> pf pp "eq_inst_%i.%s" v i.name
    | EqBvSl (i, s, e) -> pf pp "eq_bv_sl_%a[%i:%i]" Pretty.pp_sliceable_raw i s e
    | EqBv e -> pf pp "eq_bv_%a" Pretty.pp_expr_raw e
    | Err e -> pf pp "Error: %s" e


let merge_map (map1 : (FormulaId.t , 'b, 'c) Map.t) (map2 : (FormulaId.t, 'b, 'c) Map.t) =
  let combine ~(key : FormulaId.t ) (v1 : 'b) (_ : 'b) : 'b =
    let _ = key in
    v1
  in
  Map.merge_skewed  map1 map2 ~combine:combine

let var_from_sliceable s =
  let open Sliceable in
  match s with
  | Packet(v, _)
  | Instance(v, _) -> v

let rec get_var expr = 
  let open Expression in
  let check_vars v1 v2 =
    match v1 with
    | Ok a1 -> (
      match v2 with
      | Ok a2 -> (
        if phys_equal a1 a2 
          then Ok a1
          else Error (Error.of_string "Found conflictng vars"))
      | Error _ -> Ok a1)
    | Error _ -> (
      match v2 with
      | Ok a2 -> (Ok a2)
      | Error _ -> Error (Error.of_string "No valid vars found"))
  in
  match expr with
  | ArithExpr(Length(v, _)) -> Ok(v)
  | ArithExpr(Plus(arith1, arith2)) -> (
    let a1_res = get_var (ArithExpr (arith1)) in
    let  a2_res = get_var (ArithExpr (arith2)) in
    check_vars a1_res a2_res)
  | BvExpr(Concat(bv1, bv2))
  | BvExpr(Minus(bv1, bv2)) -> (
    let b1_res = get_var (BvExpr (bv1)) in
    let  b2_res = get_var (BvExpr (bv2)) in
    check_vars b1_res b2_res)
  | ArithExpr(Num _)
  | BvExpr(Bv(_)) -> Error (Error.of_string "No var found")
  | BvExpr(Slice(s, _, _)) -> Ok (var_from_sliceable s)
  | BvExpr(Packet(v, _)) -> Ok v

let get_subs_expr exp =
  (* Log.debug (fun m -> m "@[Finding substitution for %a @]" Pretty.pp_expr_raw exp); *)
  let open Expression in
  let rec get_exp e = 
    match e with
    | ArithExpr (Plus (a1, a2)) -> (
      let opt1 = get_exp (ArithExpr a1) in
      match opt1 with
      | Some _ -> opt1
      | None ->  get_exp (ArithExpr a2))
    | ArithExpr (Length (_)) ->  Some e
    | ArithExpr (Num (_)) ->  None
    | BvExpr (Concat (b1, b2)) -> (
      let opt1 = get_exp (BvExpr b1) in
      let opt2 = get_exp (BvExpr b2) in
      match (opt1, opt2) with
        | Some BvExpr Packet _, Some BvExpr Slice _ -> opt1
        | Some BvExpr Packet _, Some BvExpr Packet _
        | Some BvExpr Slice _, Some BvExpr Packet _ -> opt2
        | Some _ , None ->  opt1
        | None , Some _ -> opt2
        | _ -> None)
    | BvExpr (Slice (_)) -> Some e
    | BvExpr (Packet (_)) -> Some e
    | BvExpr (Minus (_))
    | BvExpr (Bv (_)) -> None
  in
  let exp_o = get_exp exp in
  match exp_o with
  | Some e -> 
      (* Log.debug (fun m -> m "@[Found: %a @]" Pretty.pp_expr_raw e);  *)
      e
  | None -> 
      (* Log.debug (fun m -> m "@[Nothing found, returning: %a @]" Pretty.pp_expr_raw exp); *)
      exp

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
  Log.debug (fun m -> m "====== Building substitution map ======");
  let update_instance m_in i_exp exp = 
    let open FormulaId in
    match i_exp with
    | Sliceable.Instance(var, inst) -> (
      let k_i = EqInst (var, inst) in
      (* Log.debug (fun m -> m "@[Searching for %a@]" pp_fromula_id k_i); *)
      let inst_opt = Map.find m_in k_i in
      let data =
        match inst_opt with
        | Some inst -> 
          (* Log.debug (fun m -> m "@[Found %a@]" Pretty.pp_form_raw inst); *)
          And(inst, exp)
        | None -> 
          (* Log.debug (fun m -> m "@[Nothing found@]"); *)
          exp
        in
        Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k_i Pretty.pp_form_raw  data);
        let m_t = Map.set m_in ~key:k_i ~data:data in
        (* Log.debug (fun m -> m "@[Retruning: %s@]" (Sexp.to_string_hum (sexp_of_fid_map  m_t))); *)
        m_t)
    | _ -> (
      Log.debug (fun m -> m "@[Nothing to update since %a is no instance@]" Pretty.pp_sliceable_raw i_exp);
      m_in)
  in
  let rec ext f m_in : (FormulaId.t, Formula.t , FormulaId.comparator_witness) Core.Map.t =
    let open FormulaId in
    match f with
    | And(f1, f2) -> 
      let m_tmp1 = ext f1 m_in in
      ext f2 m_tmp1

      (* x.τ.valid == y.τ.valid *)
    | Or(And(Neg(IsValid(v1, i1)),Neg(IsValid(_))), And(IsValid(_),IsValid(_))) ->
      let k = ValidEqual(v1, i1) in
      Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw  f);
      Map.set m_in ~key:k ~data:f

      (* x.τ == y.τ *)
    | Or(And(Neg(IsValid(v1, i1)),Neg(IsValid(_))), And(And(IsValid(_),IsValid(_)), And(_)))
    | Or(And(Neg(IsValid(v1, i1)),Neg(IsValid(_))), And(And(IsValid(_),IsValid(_)), Eq (BvExpr(_), BvExpr(_)))) -> 
      let k = InstEqual (v1, i1) in
      Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw  f);
      Map.set m_in ~key:k ~data:f

      (* true --> ignore *)
    | True -> m_in

    | Gt (exp1, _) -> (
      let subs_exp = get_subs_expr exp1 in
      match subs_exp with
      | ArithExpr _ ->  
        let k = GtExp exp1 in
        Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw  f);
        Map.set m_in ~key:k ~data:f
      | _ -> m_in)

    | Eq (exp1, _) -> (
      let subs_exp = get_subs_expr exp1 in
      match subs_exp with
      | BvExpr(Slice(inst, hi, lo)) -> (
        let k = EqBvSl (inst, hi, lo) in
        let m_in = update_instance m_in inst f in
        Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw  f);
        Map.set m_in ~key:k ~data:f)
      | BvExpr _ ->  
        let k = EqBv subs_exp in
        Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw  f);
        Map.set m_in ~key:k ~data:f
      | ArithExpr _ ->  
        let k = EqExp subs_exp in
        Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw  f);
        Map.set m_in ~key:k ~data:f)

      (* x.τ.valid  *)
    | Neg(IsValid(v, i)) -> 
      let k = Valid (v, i, false) in
      Log.debug(fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw f);
      Map.set m_in ~key:k ~data:f


    | IsValid(v, i) -> 
      let k = Valid (v, i, true) in
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


let rec simplify_formula form (m_in : (FormulaId.t , Formula.t , FormulaId.comparator_witness) Map.t) : Formula.t =
  let result = 
    let open FormulaId in
    match form with
    | And(f1, f2) -> Ok (And(simplify_formula f1 m_in, simplify_formula  f2 m_in))
    | Or(And(Neg(IsValid(v1, i1)),Neg(IsValid(_))), And(IsValid(_),IsValid(_))) -> (
      let valid_opt = Map.find m_in (Valid(v1, i1, true)) in
      let invalid_opt = Map.find m_in (Valid(v1, i1, false)) in
      match  (valid_opt, invalid_opt) with
      | Some _, None -> 
        let smpl = IsValid(v1, i1) in
        Log.debug (fun m -> m "@[--> replaced @ %a @ by@ %a@]" Pretty.pp_form_raw form Pretty.pp_form_raw smpl);
        Ok smpl
      | None, Some _ -> 
        let smpl = Neg(IsValid(v1, i1)) in
        Log.debug (fun m -> m "@[--> replaced @ %a @ by@ %a@]" Pretty.pp_form_raw form Pretty.pp_form_raw smpl);
        Ok smpl
      | Some _, Some _ -> Error (Error.of_string "Valid and Invalid entry found")
      | _ -> Ok(form))
      
    | Or(And(Neg(IsValid(v1, i1)),Neg(IsValid(v2, i2))), And(And(IsValid(v3, i3),IsValid(v4, i4)), f_r)) -> (
      let f_l_neg = And(Neg(IsValid(v1, i1)),Neg(IsValid(v2, i2))) in
      let f_l_pos = And(IsValid(v3, i3),IsValid(v4, i4)) in
      let f_l = Or(f_l_neg, f_l_pos)in
      let smpl_l =  simplify_formula f_l m_in in
      let smpl_r = simplify_formula f_r m_in in
      match smpl_l with
      | Neg(IsValid(_)) | IsValid(_) -> Ok(And(smpl_l, smpl_r))
      | _ -> Ok(Or(f_l_neg, And(f_l_pos, smpl_r))))
    
    | Eq(exp1, exp2) -> (
      let subs_id =
        match exp2 with
        | ArithExpr Length (_, pkt) -> Some (EqExp(ArithExpr(Length(0, pkt))))
        | BvExpr Slice(s, hi, lo) -> (
          match s with
          | Packet (_,p) -> Some (EqBv (BvExpr (Slice (Packet (0,p), hi, lo))))
          | Instance (_, i) -> Some (EqBv (BvExpr (Slice (Instance (0,i), hi, lo)))))
        | BvExpr Packet (_, p) -> Some (EqBv (BvExpr (Packet (0,p))))
        | _ -> None 
      in
      match subs_id with
      | Some id -> (
        let%bind subs = Core.Map.find_or_error m_in id in
        let%bind substitution_l = 
          match subs with
          | Eq (subs_l, _)
          | Gt (subs_l, _) -> Ok subs_l
          | _ -> Error (Error.of_string "Nothing to replace")
        in 
        Log.debug (fun m -> m "@[subs_l: %a@]" Pretty.pp_expr_raw substitution_l); 
        let%bind substitution_r = 
          match subs with
          | Eq (_ , subs_r)
          | Gt (_, subs_r) -> Ok subs_r
          | _ -> Error (Error.of_string "Nothing to replace")
        in
        Log.debug (fun m -> m "@[subs_r: %a@]" Pretty.pp_expr_raw substitution_r); 
        let%bind exp_old = 
          match id with
          | EqBv exp
          | EqExp exp
          | GtExp exp -> Ok exp
          | _ -> Error (Error.of_string "Unexpected FormulaId")
        in
        Log.debug (fun m -> m "@[exp_old: %a@]" Pretty.pp_expr_raw exp_old);
        let%bind exp_new = replace_expression substitution_l exp_old exp1
        in
        Log.debug (fun m -> m "@[--> replaced @ %a @ by@ %a@ in %a@]" 
        Pretty.pp_expr_raw exp_old 
        Pretty.pp_expr_raw exp1 
        Pretty.pp_expr_raw substitution_l);
        Ok (Eq(exp_new, substitution_r)))
      | _ -> Ok form)
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
      |Refinement(s,ht,f) -> 
        Log.debug (fun m -> m "====== Simplifying formula ======");
        Ok (Refinement(s, ht, simplify_formula f subs_map))
      |Choice(Refinement(s1,ht1,f1), Refinement(s2,ht2,f2)) -> 
        Ok (Choice(Refinement(s1, ht1, simplify_formula f1 subs_map), Refinement(s2, ht2, simplify_formula f2 subs_map)))
      | _ ->  Error (Error.of_string "h is not a Refinement"))   
    | _ -> Error (Error.of_string "hty is not a substitution"))
  in
  match result with
  | Ok ht -> 
    Log.debug (fun m -> m "@[Simplfied %a@]" Pretty.pp_header_type_raw hty);
    Log.debug (fun m -> m "@[Resulting hty %a@]" Pretty.pp_header_type_raw ht);
    ht
  | _ -> hty 
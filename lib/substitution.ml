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
      | EqArith of Expression.t
      | EqVal of Expression.t
      | Err of string
      [@@deriving compare, sexp] 
  end
  include T
  include Comparable.Make(T)
end

let pp_fromula_id (pp : Format.formatter) (fid :FormulaId.t) = 
  let open Fmt in
  match fid with
    | Invalid i -> pf pp "invalid_%s" i.name
    | Valid i -> pf pp "valid_%s" i.name
    | InstEqual i -> pf pp "inst_equal_%s" i.name
    | EqBv e -> pf pp "eq_bv_%a" Pretty.pp_expr_raw e
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
    | And(f1, f2) -> merge_map (ext f1 m_in) (ext f2 m_in) 
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
          let open Expression in
          match o with 
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
      Map.empty(module FormulaId)
  in
  let map = Map.empty(module FormulaId) in
  ext form map

let rec simplify_formula (form : Formula.t) (map : (FormulaId.t , Formula.t , FormulaId.comparator_witness) Map.t) : Formula.t =
    let result = 
      match form with
      | And(f1, f2) -> Ok (And(simplify_formula f1 map, simplify_formula  f2 map))
      | Or(And(Neg(IsValid(v1, i1)),Neg(IsValid(_))), And(And(IsValid(_),IsValid(_)), Eq (BvExpr(_), BvExpr(_)))) -> (
        let%bind _ = Map.find_or_error map (Valid i1) in
        let smpl = IsValid(v1, i1) in
        Log.debug (fun m -> m "@[replaced @ %a @ by@ %a@]" Pretty.pp_form_raw form Pretty.pp_form_raw smpl);
        Ok smpl)
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
        let%bind exp_new = replace_expression substitution_l exp_old exp1
        in
        Ok (Eq(exp_new, substitution_r))
      | _ -> Ok form
    in 
    match result with 
    | Ok f -> f
    | _ -> form

let simplify (hty : HeapType.t) : HeapType.t = 
  let hty = Simplify.fold_refinements hty in
  Log.debug (fun m -> m "@[Simplifying %a@]" Pretty.pp_header_type_raw hty);
  let smpl hty = 
    match hty with
    | Substitution(h, str, subs) -> (
      Log.debug (fun m -> m "@[Substituting %s@]" str);
      match h with
        | Refinement(s,ht,f) -> (
          match subs with
          Refinement(_,_,f_subs) -> (
          let subs_map = extract_to_map f_subs in
          Refinement(s, ht, simplify_formula f subs_map))
        | _ -> (
          Log.debug (fun m -> m "@[subs is not a Refinement: %a@]" Pretty.pp_header_type_raw subs);
          hty))
      | _ -> (
        Log.debug (fun m -> m "@[h is not a Refinement: %a@]" Pretty.pp_header_type_raw h);
        h) 
    )
    | _ -> hty
  in
  smpl hty
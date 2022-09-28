open Core
open Syntax
open Formula
open Expression

let rec fold_plus (term : Expression.arith) =
  match term with
  | Plus (Num m, Num n) -> Num (m + n)
  | Plus (Plus (t, Num m), Num n) -> fold_plus (Plus (t, Num (m + n)))
  | _ as t -> t
  
let rec fold_concat t =
  match t with
  | Concat (Bv Nil, t2) -> fold_concat t2
  | Concat (t1, Bv Nil) -> fold_concat t1
  | Concat (Bv a, Bv b) -> Bv (BitVector.concat a b)
  | Concat (Slice (s1, ll, lr), Slice (s2, rl, rr)) ->
    if [%compare.equal: Sliceable.t] s1 s2 && lr = rl then
      Slice (s1, ll, rr)
    else
      t
  | Concat (Bv a, Concat (Bv b, t2)) ->
    fold_concat (Concat (Bv (BitVector.concat a b), t2))
  | Concat
      ((Slice (s1, ll, lr) as t1), Concat ((Slice (s2, rl, rr) as t21), t22)) ->
    if [%compare.equal: Sliceable.t] s1 s2 && lr = rl then
      fold_concat (Concat (Slice (s1, ll, rr), t22))
    else
      Concat (t1, fold_concat (Concat (t21, t22)))
  | Concat
      (Concat ( t11, (Slice (s1, ll, lr) as t12)), (Slice (s2, rl, rr) as t2)) ->
    if [%compare.equal: Sliceable.t] s1 s2 && lr = rl then
      fold_concat (Concat (t11, Slice (s1, ll, rr)))
    else
      Concat (fold_concat (Concat (t11, t12)), t2)
  | Concat (t1, t2) -> Concat (fold_concat t1, fold_concat t2)
  | _ -> t

let simplify_expr (expr : Expression.t) =
  match expr with
  | ArithExpr e -> ArithExpr (fold_plus e)
  | BvExpr e -> BvExpr (fold_concat e)

(* let simplify_expr (expr : Formula.t) = let rec aux e0 k = match e0 with |
   TmEq (tm1, tm2) -> k (TmEq (simplify_term tm1, simplify_term tm2)) | Neg e1
   -> aux e1 (fun e1' -> k (Neg e1')) | And (e1, e2) -> aux e1 (fun e1' -> aux
   e2 (fun e2' -> k (And (e1', e2')))) | _ as e' -> k e' in aux expr (fun x ->
   x) *)

let expr_equal = [%compare.equal: Formula.t]

let rec simplify_form (form : Formula.t) =
  match form with
  | Eq (tm1, tm2) -> Eq (simplify_expr tm1, simplify_expr tm2)
  | Gt (tm1, tm2) -> Gt (simplify_expr tm1, simplify_expr tm2)
  | Neg e1 -> Neg (simplify_form e1)
  | And (True, e) -> simplify_form e
  | And (e, True) -> simplify_form e
  | And (e1, And (e2, e3)) ->
    if expr_equal e1 e2 then
      simplify_form (And (e1, e3))
    else
      And (simplify_form e1, simplify_form (And (e2, e3)))
  | And (e1, e2) -> And (simplify_form e1, simplify_form e2)
  | _ as e' -> e'

module FormulaSet = Set.Make (Formula)

let rec fold_refinements (header_type : HeapType.t) =
  let open HeapType in
  match header_type with
  | Sigma (x, hty1, hty2) ->
    Sigma (x, fold_refinements hty1, fold_refinements hty2)
  | Choice (hty1, hty2) -> Choice (fold_refinements hty1, fold_refinements hty2)
  | Refinement (x, hty, e) ->
    let hty', exprs = collect_exprs hty FormulaSet.empty in
    let e' = Set.fold exprs ~init:e ~f:(fun acc expr -> And (expr, acc)) in
    Refinement (x, fold_refinements hty', simplify_form e')
  | Substitution (hty1, x, hty2) ->
    Substitution (fold_refinements hty1, x, fold_refinements hty2)
  | _ as hty -> hty

and collect_exprs (header_type : HeapType.t) (acc : FormulaSet.t) =
  let rec aux expr acc =
    match expr with
    | And (e1, e2) -> Set.union (aux e1 acc) (aux e2 acc)
    | _ as e -> Set.add acc e
  in
  match header_type with
  | Refinement (_, hty, e) -> collect_exprs hty (aux e acc)
  | _ as hty -> (hty, acc)

let rec simplify_command (cmd : Command.t) =
  match cmd with
  | Seq (Skip, c) -> simplify_command c
  | Seq (c, Skip) -> simplify_command c
  | Seq (c1, c2) -> Command.Seq (simplify_command c1, simplify_command c2)
  | If (e, c1, c2) -> Command.If (e, simplify_command c1, simplify_command c2)
  | Ascription (c, x, hty_in, hty_out) ->
    Command.Ascription (simplify_command c, x, hty_in, hty_out)
  | _ as c -> c

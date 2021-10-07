open Core_kernel
open Syntax
open Expression
open Term

let rec fold_plus (term : Term.t) =
  match term with
  | Plus (Num m, Num n) -> Num (m + n)
  | Plus (Plus (t, Num m), Num n) -> fold_plus (Plus (t, Num (m + n)))
  | _ as t -> t

(* TODO: - nested concats: <0>@(<0>@slice) -> <00> @ slice - s[0:1]@s[1:2] ->
   s[0:2] *)
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
  | Concat (t1, t2) -> Concat (fold_concat t1, fold_concat t2)
  | _ -> t

let simplify_term (term : Term.t) = fold_concat (fold_plus term)

(* let simplify_expr (expr : Expression.t) = let rec aux e0 k = match e0 with |
   TmEq (tm1, tm2) -> k (TmEq (simplify_term tm1, simplify_term tm2)) | Neg e1
   -> aux e1 (fun e1' -> k (Neg e1')) | And (e1, e2) -> aux e1 (fun e1' -> aux
   e2 (fun e2' -> k (And (e1', e2')))) | _ as e' -> k e' in aux expr (fun x ->
   x) *)

let expr_equal = [%compare.equal: Expression.t]

let rec simplify_expr (expr : Expression.t) =
  match expr with
  | TmEq (tm1, tm2) -> TmEq (simplify_term tm1, simplify_term tm2)
  | TmGt (tm1, tm2) -> TmGt (simplify_term tm1, simplify_term tm2)
  | Neg e1 -> Neg (simplify_expr e1)
  | And (True, e) -> simplify_expr e
  | And (e, True) -> simplify_expr e
  | And (e1, And (e2, e3)) ->
    if expr_equal e1 e2 then
      simplify_expr (And (e1, e3))
    else
      And (simplify_expr e1, simplify_expr (And (e2, e3)))
  | And (e1, e2) -> And (simplify_expr e1, simplify_expr e2)
  | _ as e' -> e'

module ExpressionSet = Set.Make (Expression)

let rec fold_refinements (header_type : HeapType.t) =
  let open HeapType in
  match header_type with
  | Sigma (x, hty1, hty2) ->
    Sigma (x, fold_refinements hty1, fold_refinements hty2)
  | Choice (hty1, hty2) -> Choice (fold_refinements hty1, fold_refinements hty2)
  | Refinement (x, hty, e) ->
    let hty', exprs = collect_exprs hty ExpressionSet.empty in
    let e' = Set.fold exprs ~init:e ~f:(fun acc expr -> And (expr, acc)) in
    Refinement (x, fold_refinements hty', simplify_expr e')
  | Substitution (hty1, x, hty2) ->
    Substitution (fold_refinements hty1, x, fold_refinements hty2)
  | _ as hty -> hty

and collect_exprs (header_type : HeapType.t) (acc : ExpressionSet.t) =
  let rec aux expr acc =
    match expr with
    | And (e1, e2) -> Set.union (aux e1 acc) (aux e2 acc)
    | _ as e -> Set.add acc e
  in
  match header_type with
  | Refinement (_, hty, e) -> collect_exprs hty (aux e acc)
  | _ as hty -> (hty, acc)

let rec simplify_command (cmd : command) =
  match cmd with
  | Seq (Skip, c) -> simplify_command c
  | Seq (c, Skip) -> simplify_command c
  | Seq (c1, c2) -> Seq (simplify_command c1, simplify_command c2)
  | If (e, c1, c2) -> If (e, simplify_command c1, simplify_command c2)
  | Ascription (c, x, hty_in, hty_out) ->
    Ascription (simplify_command c, x, hty_in, hty_out)
  | _ as c -> c

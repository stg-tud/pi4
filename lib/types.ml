open Core_kernel
open Syntax

module Distance = struct
  type t = int * int [@@deriving compare, sexp]
end

module DistanceSet = Set.Make (Distance)

let rec collect_free_binders (header_type : HeapType.t)
    (init_ctx : Env.context) =
  collect_free_binders_from_header_type init_ctx header_type DistanceSet.empty

and collect_free_binders_from_header_type (ctx : Env.context)
    (header_type : HeapType.t) (acc : DistanceSet.t) =
  match header_type with
  | Nothing
  | Empty
  | Top ->
    acc
  | Choice (hty1, hty2) ->
    let acc' = collect_free_binders_from_header_type ctx hty1 acc in
    collect_free_binders_from_header_type ctx hty2 acc'
  | Sigma (x, hty1, hty2) ->
    let acc' = collect_free_binders_from_header_type ctx hty1 acc in
    let ctx' = Env.add_binding ctx x (VarBind hty1) in
    collect_free_binders_from_header_type ctx' hty2 acc'
  | Refinement (x, hty, e) ->
    let acc' = collect_free_binders_from_header_type ctx hty acc in
    let ctx' = Env.add_binding ctx x (VarBind hty) in
    collect_free_binders_from_expr ctx' e acc'
  | Substitution (hty1, x, hty2) ->
    let acc' = collect_free_binders_from_header_type ctx hty2 acc in
    let ctx' = Env.add_binding ctx x (VarBind hty2) in
    collect_free_binders_from_header_type ctx' hty1 acc'

and collect_free_binders_from_expr (ctx : Env.context) (expr : Expression.t)
    (acc : DistanceSet.t) =
  match expr with
  | True
  | False ->
    acc
  | IsValid (x, _) ->
    add_binder_if_free ctx x acc
  | TmEq (tm1, tm2)
  | TmGt (tm1, tm2) ->
    let acc' = collect_free_binders_from_term ctx tm1 acc in
    collect_free_binders_from_term ctx tm2 acc'
  | Neg e -> collect_free_binders_from_expr ctx e acc
  | And (e1, e2)
  | Or (e1, e2)
  | Implies (e1, e2) ->
    let acc' = collect_free_binders_from_expr ctx e1 acc in
    collect_free_binders_from_expr ctx e2 acc'

and add_binder_if_free (ctx : Env.context) (x : int) (acc : DistanceSet.t) =
  let ctx_length = List.length ctx in
  if x >= ctx_length then (
    let dist = x - ctx_length in
    Set.add acc (x, dist)
  ) else
    acc

and collect_free_binders_from_term (ctx : Env.context) (term : Term.t)
    (acc : DistanceSet.t) =
  match term with
  | Num _
  | Bv _ ->
    acc
  | Length (x, _) -> add_binder_if_free ctx x acc
  | (Plus (tm1, tm2) | Minus(tm1, tm2) | Concat (tm1, tm2)) ->
    let acc' = collect_free_binders_from_term ctx tm1 acc in
    collect_free_binders_from_term ctx tm2 acc'
  | (Slice (Packet (x, _), _, _) | Slice (Instance (x, _), _, _)) ->
    add_binder_if_free ctx x acc
  | Packet (x, _) -> add_binder_if_free ctx x acc

let var_not_bound x ctx = x >= List.length ctx

let rec contains_free_vars (header_type : HeapType.t) : bool =
  free_vars_header_type [] header_type

and free_vars_header_type (ctx : Env.context) (hty : HeapType.t) : bool =
  match hty with
  | Nothing
  | Empty
  | Top -> false
  | Choice (hty1, hty2) ->
    free_vars_header_type ctx hty1 || free_vars_header_type ctx hty2
  | Sigma (x, hty1, hty2) ->
    let ctx' = Env.add_binding ctx x (VarBind hty1) in
    free_vars_header_type ctx hty1 || free_vars_header_type ctx' hty2
  | Refinement (x, hty, e) ->
    let ctx' = Env.add_binding ctx x (VarBind hty) in
    free_vars_header_type ctx hty || free_vars_expr ctx' e
  | Substitution (hty1, x, hty2) ->
    let ctx' = Env.add_binding ctx x (VarBind hty2) in
    free_vars_header_type ctx hty2 || free_vars_header_type ctx' hty1

and free_vars_expr (ctx : Env.context) (expr : Expression.t) : bool =
  match expr with
  | True
  | False ->
    false
  | IsValid (x, _) -> var_not_bound x ctx
  | TmEq (tm1, tm2) -> free_vars_term ctx tm1 || free_vars_term ctx tm2
  | TmGt (tm1, tm2) -> free_vars_term ctx tm1 || free_vars_term ctx tm2
  | Neg e -> free_vars_expr ctx e
  | And (e1, e2)
  | Or (e1, e2)
  | Implies (e1, e2) ->
    free_vars_expr ctx e1 || free_vars_expr ctx e2

and free_vars_term (ctx : Env.context) (term : Term.t) : bool =
  match term with
  | Num _
  | Bv _ ->
    false
  | Length (x, _) -> var_not_bound x ctx
  | Plus (tm1, tm2) | Minus (tm1, tm2) -> free_vars_term ctx tm1 || free_vars_term ctx tm2
  | Concat (tm1, tm2) -> free_vars_term ctx tm1 || free_vars_term ctx tm2
  | Slice (Packet (x, _), _, _) -> var_not_bound x ctx
  | Slice (Instance (x, _), _, _) -> var_not_bound x ctx
  | Packet (x, _) -> var_not_bound x ctx

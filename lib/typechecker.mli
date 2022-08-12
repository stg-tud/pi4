open Syntax

module TypecheckingResult : sig
  type t =
    | TypeError of string
    | Success
  [@@deriving compare, sexp]

  val is_error : t -> bool
  val pp : Format.formatter -> t -> unit
end

module type S = sig
  val check_type :
    ?enable_includes_cache:bool ->
    Command.t ->
    pi_type ->
    HeaderTable.t ->
    TypecheckingResult.t
end

module type Checker = sig
  val init : unit -> unit

  val compute_type :
    Command.t ->
    string * HeapType.t ->
    Env.context ->
    HeaderTable.t ->
    ( HeapType.t,
      [> `TypeError of string
      | `EncodingError of string
      | `VariableLookupError of string
      ] )
    result

  val check_subtype :
    HeapType.t ->
    HeapType.t ->
    Env.context ->
    HeaderTable.t ->
    ( bool,
      [> `TypeError of string
      | `EncodingError of string
      | `VariableLookupError of string
      ] )
    result
end

module CompleteChecker : functor
  (BV : sig
     val maxlen : int
   end)
  -> Checker

module SemanticChecker : functor
  (BV : sig
     val maxlen : int
   end)
  -> Checker

module Make : functor (C : Checker) -> S

module ExprChecker : functor (P : Prover.S) -> sig
  val check_expr :
    HeaderTable.t ->
    Env.context ->
    HeapType.t ->
    Expression.t ->
    ( ty,
      [> `TypeError of string
      | `EncodingError of string
      | `VariableLookupError of string
      ] )
    result
end

module FormChecker : functor (P : Prover.S) -> sig
  val check_form :
    HeaderTable.t ->
    Env.context ->
    HeapType.t ->
    Formula.t ->
    ( ty,
      [> `TypeError of string
      | `EncodingError of string
      | `VariableLookupError of string
      ] )
    result
end

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
  val check_type : command -> ty -> HeaderTable.t -> TypecheckingResult.t
end

module type Checker = sig
  val compute_type :
    command ->
    string * HeapType.t ->
    Env.context ->
    HeaderTable.t ->
    (HeapType.t, string) result

  val check_subtype :
    HeapType.t ->
    HeapType.t ->
    Env.context ->
    HeaderTable.t ->
    (bool, string) result
end

module type Chomp = sig
  include Checker

  val chomp1 : HeapType.t -> Env.context -> int -> HeapType.t

  val chomp_e1 : Expression.t -> Syntax.var -> int -> Expression.t

  val chomp_ref1 : HeapType.t -> var -> int -> HeapType.t

  val chomp_t1 : Term.t -> Syntax.var -> int -> Term.t

  val heap_tref1 : Term.t -> int -> var -> Instance.t -> int -> Term.t
end

module CompleteChecker : functor
  (BV : sig
     val maxlen : int
   end)
  -> Chomp

module SimpleChecker : Checker

module Make : functor (C : Checker) -> S
module MakeSSAChecker : functor (C : Checker) -> S

val typeof_tm : Term.t -> (ty, string) result

val typeof_exp : Expression.t -> (ty, string) result

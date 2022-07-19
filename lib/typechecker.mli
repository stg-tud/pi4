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
    Command.t -> 
    ?smpl_subs:bool -> 
    ?incl_cache:bool ->
    ?len_cache:bool ->
    ?dynamic_maxlen:bool ->
    pi_type -> 
    HeaderTable.t -> 
    TypecheckingResult.t
end

module type Checker = sig

  val set_maxlen :
    var -> unit

  val reset_cache :
    unit -> unit

  val compute_type :
    Command.t ->
    ?smpl_subs:bool ->
    ?init_pkt_in:(var)option ->
    ?init_pkt_out:(var)option ->
    ?incl_cache:bool ->
    ?len_cache:bool ->
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

module SemanticChecker : functor
  (BV : sig
     val maxlen : int ref
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

open Syntax
open Z3

val make_prover : string -> unit

val default_tactic : Smtlib.tactic

module type S = sig
  val check_subtype :
    HeapType.t ->
    HeapType.t ->
    Env.context ->
    HeaderTable.t ->
    (bool, string) result

  val check_subtype_with_tactic :
    HeapType.t ->
    HeapType.t ->
    Env.context ->
    HeaderTable.t ->
    Smtlib.tactic ->
    (bool, string) result

  val has_model_with_tactic :
    HeapType.t ->
    Env.context ->
    HeaderTable.t ->
    Z3.Smtlib.tactic ->
    (bool, string) result
end

module Make : functor (Enc : Encoding.S) -> S

open Syntax

val chomp :
  HeapType.t -> Env.context -> Instance.t -> HeaderTable.t -> HeapType.t

val chomp_rec :
  HeapType.t ->
  Env.context ->
  int ->
  var ->
  Instance.t ->
  int ->
  HeaderTable.t ->
  HeapType.t

val chomp1 : HeapType.t -> Env.context -> int -> HeapType.t

val chomp_e1 : Formula.t -> Syntax.var -> int -> Formula.t

val chomp_ref1 : HeapType.t -> var -> int -> HeapType.t

val chomp_t1 : Expression.t -> Syntax.var -> int -> Expression.t

val heap_eref1 : Formula.t -> int -> var -> Instance.t -> int -> Formula.t

val heap_tref1 : Expression.t -> int -> var -> Instance.t -> int -> Expression.t

val heap_ref1 : HeapType.t -> int -> var -> Instance.t -> int -> HeapType.t

module Optimized : functor (P : Prover.S) -> sig
  val chomp :
    HeapType.t ->
    Env.context ->
    Instance.t ->
    HeaderTable.t ->
    ( HeapType.t,
      [> `EncodingError of string | `VariableLookupError of string ] )
    result
end

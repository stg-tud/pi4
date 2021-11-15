open Syntax
open Z3

val freshen_binders : HeapType.t -> (string -> string) -> HeapType.t

val true_ : Smtlib.term

val false_ : Smtlib.term

val id_dedup :
  (Smtlib.identifier * Smtlib.sort) list ->
  (Smtlib.identifier * Smtlib.sort) list

module type S = sig
  val equal : string -> string -> HeaderTable.t -> Smtlib.term

  val header_type_to_smt :
    HeaderTable.t ->
    Env.context ->
    string ->
    HeapType.t ->
    ( Smtlib.term,
      [> `EncodingError of string | `VariableLookupError of string ] )
    result

  val smt_consts :
    HeapType.t ->
    string ->
    HeaderTable.t ->
    (Smtlib.identifier * Smtlib.sort) list
end

module type Config = sig
  val maxlen : int
end

module FixedWidthBitvectorEncoding : functor (Config : Config) -> S

module DefaultEncoding : S

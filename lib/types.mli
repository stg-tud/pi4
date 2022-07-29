open Core
open Syntax

module Distance : sig
  type t = int * int [@@deriving compare, sexp]
end

module DistanceSet : Set.S with type Elt.t = Distance.t

val contains_free_vars : HeapType.t -> bool

val collect_free_binders : HeapType.t -> Env.context -> DistanceSet.t

open Syntax

type binding =
  | NameBind
  | VarBind of HeapType.t

type context = (string * binding) list

val add_binding : context -> string -> binding -> context

val index_to_name : context -> int -> string

val is_name_bound : context -> string -> bool

val pick_fresh_name : context -> string -> string

val index_to_binding : context -> int -> (string * binding, string) result

val name_to_index : context -> string -> (int, string) result

val name_to_index_exn : context -> string -> int

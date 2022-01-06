open Syntax

type binding =
  | NameBind
  | VarBind of HeapType.t
[@@deriving sexp]

type context = (string * binding) list

val add_binding : context -> string -> binding -> context

val index_to_name : context -> int -> (string, [> `VariableLookupError of string]) result

val index_to_name_exn : context -> int -> string

val is_name_bound : (string * 'a) list -> string -> bool

val pick_fresh_name_f : (string * 'a) list -> f:(string -> string) -> string -> string

val pick_fresh_name : context -> string -> string

val index_to_binding : context -> int -> (string * binding, [> `VariableLookupError of string ]) result

val name_to_index : context -> string -> (int, [> `IdentifierUnboundError of string ]) result

val name_to_index_exn : context -> string -> int

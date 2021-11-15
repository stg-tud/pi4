open Syntax

val heap_type_of_string :
  string -> HeaderTable.t -> Env.context -> HeapType.t

val parse_heap_type : string -> HeaderTable.t -> Env.context -> HeapType.t

val parse_command : string -> HeaderTable.t -> command

val parse_program : string -> Program.t

val parse_program_from_file : string -> Program.t

val read_file : string -> string

val parse_type : string -> HeaderTable.t -> ty

val parse_type_from_file : string -> HeaderTable.t -> ty  

val parse_instance : string -> Instance.t

val parse_smt_tactic : string -> Z3.Smtlib.tactic

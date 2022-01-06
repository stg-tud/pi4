open Syntax

type error = [ `SyntaxError of string ]

val parse_heap_type : HeaderTable.t -> Env.context -> string -> HeapType.t
val parse_command : string -> HeaderTable.t -> Command.t
val parse_program : string -> Program.t
val parse_program_from_file : string -> Program.t
val read_file : string -> string
val parse_type : string -> HeaderTable.t -> pi_type
val parse_type_from_file : string -> HeaderTable.t -> pi_type
val parse_instance : string -> (Instance.t, [> `SyntaxError of string ]) result
val parse_instance_exn : string -> Instance.t
val parse_smt_tactic : string -> Z3.Smtlib.tactic

val parse_annotation :
  Syntax.HeaderTable.t -> string -> (Syntax.Annotation.t, [> error ]) result

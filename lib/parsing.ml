open Core_kernel

let heap_type_of_string header_type_str header_table ctx =
  let lexbuf = Lexing.from_string header_type_str in
  (Parser.heap_type Lexer.read_token lexbuf) header_table ctx

let parse_command cmd header_table =
  let lexbuf = Lexing.from_string cmd in
  (Parser.command Lexer.read_token lexbuf) header_table

let parse_program cmd_str =
  let lexbuf = Lexing.from_string cmd_str in
  Parser.program Lexer.read_token lexbuf

let read_file file_name =
  In_channel.with_file file_name ~f:(fun input -> In_channel.input_all input)

let parse_program_from_file file =
  let input = read_file file in
  parse_program input

let parse_type ty_str header_table =
  let lexbuf = Lexing.from_string ty_str in
  (Parser.ty Lexer.read_token lexbuf) header_table

let parse_type_from_file file header_table =
  let ty_str = read_file file in
  parse_type ty_str header_table

let parse_instance inst_str =
  let lexbuf = Lexing.from_string inst_str in
  Parser.instance Lexer.read_token lexbuf

let parse_heap_type (input : string) (header_table : Syntax.HeaderTable.t)
    (ctx : Env.context) =
  heap_type_of_string input header_table ctx

let parse_smt_tactic (input : string) = 
  let lexbuf = Lexing.from_string input in
  Parser.smt_tactic Lexer.read_token lexbuf

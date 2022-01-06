open Core_kernel
module I = Parser.MenhirInterpreter

type error = [ `SyntaxError of string ]

let get_lexing_position lexbuf =
  let p = Lexing.lexeme_start_p lexbuf in
  let line_number = p.Lexing.pos_lnum in
  let column = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1 in
  (line_number, column)

let get_parse_error env =
  match I.stack env with
  | (lazy Nil) -> "Invalid syntax"
  | (lazy (Cons (I.Element (state, _, _, _), _))) -> (
    try Parser_messages.message (I.number state)
    with Caml.Not_found -> "Invalid syntax")

exception Syntax_error of ((int * int) option * string)

let rec run_parser lexbuf checkpoint =
  match checkpoint with
  | I.InputNeeded _env ->
    let token = Lexer.read_token lexbuf in
    let startp = lexbuf.lex_start_p
    and endp = lexbuf.lex_curr_p in
    let checkpoint = I.offer checkpoint (token, startp, endp) in
    run_parser lexbuf checkpoint
  | I.Shifting _ | I.AboutToReduce _ ->
    let checkpoint = I.resume checkpoint in
    run_parser lexbuf checkpoint
  | I.HandlingError _env ->
    let line, pos = get_lexing_position lexbuf in
    let err = get_parse_error _env in
    raise (Syntax_error (Some (line, pos), err))
  | I.Accepted v -> v
  | I.Rejected ->
    raise (Syntax_error (None, "invalid syntax, parser rejected the input"))

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
  (Parser.pi_type Lexer.read_token lexbuf) header_table

let parse_type_from_file file header_table =
  let ty_str = read_file file in
  parse_type ty_str header_table

let parse_exn lexbuf (f : Lexing.position -> 'a I.checkpoint) =
  run_parser lexbuf (f lexbuf.lex_curr_p)

let parse lexbuf (f : Lexing.position -> 'a I.checkpoint) =
  try Ok (parse_exn lexbuf f)
  with Syntax_error (pos, err) -> (
    match pos with
    | Some (line, pos) ->
      Error
        (`SyntaxError
          (Fmt.str "Syntax error on line %d, character %d: %s" line pos err))
    | None -> Error (`SyntaxError (Fmt.str "Syntax error: %s" err)))

let parse_instance_exn s =
  let lexbuf = Lexing.from_string s in
  parse_exn lexbuf Parser.Incremental.instance

let parse_instance inst_str =
  let lexbuf = Lexing.from_string inst_str in
  parse lexbuf Parser.Incremental.instance

let parse_heap_type header_table ctx s =
  let lexbuf = Lexing.from_string s in
  (Parser.heap_type Lexer.read_token lexbuf) header_table ctx

let parse_smt_tactic (input : string) =
  let lexbuf = Lexing.from_string input in
  Parser.smt_tactic Lexer.read_token lexbuf

let parse_annotation header_table input :
    (Syntax.Annotation.t, [> `SyntaxError of string ]) result =
  let lexbuf = Lexing.from_string input in
  match parse lexbuf Parser.Incremental.annotation with
  | Ok f_parse -> Ok (f_parse header_table)
  | Error _ as e -> e

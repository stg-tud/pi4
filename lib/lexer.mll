{
  open Lexing
  open Parser

  exception SyntaxError of ((int * int) option * string)

  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = pos.pos_cnum;
                 pos_lnum = pos.pos_lnum + 1;
      }
  
  let get_lexing_position lexbuf = 
    let p = Lexing.lexeme_start_p lexbuf in
    let line_number = p.Lexing.pos_lnum in
    let column = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1 in
    (line_number, column)

  let lexing_error lexbuf msg =
    let line, column = get_lexing_position lexbuf in
    raise (SyntaxError (Some (line, column), msg))
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let int = digit+ 
let bitstring = "0b" (['0' '1']+)
let hexstring = "0x" (['a'-'f' 'A'-'F' '0'-'9']+)
let id = (alpha) (alpha|digit|'_'|'\'')*
let whitespace = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule read_token = parse
| "(" { LPAREN }
| ")" { RPAREN }
| "{" { LBRACE }
| "}" { RBRACE }
| "[" { LSQUARE }
| "]" { RSQUARE }
| "." { DOT }
| ":" { COLON }
| ";" { SEMI }
| "+" { PLUS }
| "-" { MINUS }
| "!" { BANG }
| "?" { QUERY }
| "~" { TILDE }
| "&&" { AND }
| "∧" { AND }
| "|" { VBAR }
| "||" { OR }
| "∨" { OR }
| "->" { ARROW }
| "↦" { ARROW }
| "→" { ARROW }
| "=>" { DARROW }
| "⇒" { DARROW }
| "=i=" { INST_EQ }
| "=" { EQ }
| "@" { AT }
| "<" { LT }
| ">" { GT }
| whitespace { read_token lexbuf }
| "true" { TRUE }
| "false" { FALSE }
| "\\nothing" { NOTHING }
| "∅" { NOTHING }
| "\\empty" { EMPTY }
| "ε" { EMPTY }
| "\\sigma" { SIGMA }
| "Σ" { SIGMA }
| "\\top" { TOP }
| "⊤" { TOP }
| "valid" { VALID }
| "length" { LENGTH }
| "pkt_in" { PKTIN }
| "pkt_out" { PKTOUT }
| "as" { AS }
| "add" { ADD }
| "extract" { EXTRACT }
| "reset" { RESET }
| "remit" { REMIT }
| "remove" { REMOVE }
| "skip" { SKIP }
| "if" { IF }
| "else" { ELSE }
| "header" { HEADER }
| "header_type" { HEADERTYPE }
| "¬" { NEG }
| "aig" { AIG }
| "bit-blast" { BITBLAST }
| "par-or" { PAR_OR }
| "qe" { QE }
| "simplify" { SIMPLIFY }
| "solve-eqs" { SOLVE_EQS }
| "then" { THEN }
| "ufbv" { UFBV }
| "qfbv" { QFBV }
| hexstring { HEXSTRING (Lexing.lexeme lexbuf)}
| bitstring { BITSTRING (Lexing.lexeme lexbuf)}
| int { INT (int_of_string (Lexing.lexeme lexbuf)) }
| id { ID (Lexing.lexeme lexbuf) }
| newline { next_line lexbuf; read_token lexbuf }
| eof { EOF }   
| _ as bad_char { 
  lexing_error lexbuf (Printf.sprintf "Unexpected character \'%c\'" bad_char) }

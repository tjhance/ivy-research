{
open Lexing
open ExprParser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '.']*
let infix_id = ['<' '=' '~' '>']*

rule read =
  parse
  | white    { read lexbuf }
  | newline  { next_line lexbuf; EOL }
  | "bool"   { BOOL }
  | "some"   { SOME }
  | "else"   { ELSE }
  | "true"   { TRUE }
  | "false"  { FALSE }
  | "forall" { FORALL }
  | "exists" { EXISTS }
  | "~="     { DIFFERENT }
  | "->"     { RIGHT_ARROW }
  | '.'      { POINT }
  | ','      { COMMA }
  | ':'      { COLON }
  | '('      { LEFT_PARENTHESIS }
  | ')'      { RIGHT_PARENTHESIS }
  | '&'      { AND }
  | '|'      { OR }
  | '='      { EQUAL }
  | '~'      { NOT }
  | infix_id { INFIX_ID (Lexing.lexeme lexbuf) }
  | id       { ID (Lexing.lexeme lexbuf) }
  | eof      { EOF }
  | _        { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }

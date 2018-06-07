{
open Lexing
open Parser

exception SyntaxError of string
}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
(* let newlines = [' ' '\t' '\r' '\n']* *)
let qvar_id = ['A'-'Z']+
let id =
    ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '.']* ['a'-'z' 'A'-'Z' '0'-'9' '_']
  | ['a'-'z' 'A'-'Z' '_']
let infix_id = ['<' '=' '~' '>']+

rule read ignore_nls =
  parse
  | white    { read ignore_nls lexbuf }
  | newline  { Lexing.new_line lexbuf; if ignore_nls then read true lexbuf else EOL }
  | "bool"   { BOOL }
  | "some"   { SOME }
  | "else"   { ELSE }
  | "true"   { TRUE }
  | "false"  { FALSE }
  | "forall" { FORALL }
  | "exists" { EXISTS }
  | "call"   { CALL }
  | "if"     { IF }
  | "assert" { ASSERT }
  | "ensure" { ASSERT }
  | "require" { ASSUME }
  | "assume" { ASSUME }
  | "conjecture" { CONJECTURE }
  | "type"   { TYPE }
  | "action" { ACTION }
  | "returns" { RETURNS }
  | "individual" { INDIVIDUAL }
  | "function" { FUNCTION }
  | "relation" { RELATION }
  | "module" { MODULE }
  | "object" { OBJECT }
  | "instance" { INSTANCE }
  | "~="     { DIFFERENT }
  | "->"     { RIGHT_ARROW }
  | ":="     { ASSIGN }
  | '{'      { LEFT_BRACE }
  | '}'      { RIGHT_BRACE }
  | '.'      { POINT }
  | ','      { COMMA }
  | ':'      { COLON }
  | ';'      { SEMI_COLON }
  | '('      { LEFT_PARENTHESIS }
  | ')'      { RIGHT_PARENTHESIS }
  | '&'      { AND }
  | '|'      { OR }
  | '='      { EQUAL }
  | '~'      { NOT }
  | qvar_id  { QVAR_ID (Lexing.lexeme lexbuf) }
  | infix_id { INFIX_ID (Lexing.lexeme lexbuf) }
  | id       { ID (Lexing.lexeme lexbuf) }
  | eof      { EOF }
  | _        { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }

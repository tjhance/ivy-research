{
open Lexing
open Parser

exception SyntaxError of string
}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let comment = '#' | "axiom" | "isolate" | "inductive" | "export" | "extract" | "property"
let int = '-'? ['0'-'9'] ['0'-'9']*
let qvar_id = ['A'-'Z']+
let id =
    ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '.']* ['a'-'z' 'A'-'Z' '0'-'9' '_']
  | ['a'-'z' 'A'-'Z' '_']
let infix_cmp_id = ['<' '=' '~' '>']+
let infix_fun_id = ['+' '-']+

rule read ignore_nls =
  parse
  | white    { read ignore_nls lexbuf }
  | newline  { Lexing.new_line lexbuf; if ignore_nls then read true lexbuf else EOL }
  | comment  { read_until_eol ignore_nls lexbuf }
  | "bool"   { BOOL }
  | "some"   { SOME }
  | "else"   { ELSE }
  | "true"   { TRUE }
  | "false"  { FALSE }
  | "forall" { FORALL }
  | "exists" { EXISTS }
  | "call"   { CALL }
  | "if"     { IF }
  | "var"     { VAR }
  | "assert" { ASSERT }
  | "ensure" { ENSURE }
  | "require" { REQUIRE }
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
  | "instantiate" { INSTANTIATE }
  | "implement"  { IMPLEMENT }
  | "after"  { AFTER }
  | "before" { BEFORE }
  | "definition" { DEFINITION }
  | "derived" { DEFINITION }
  | "interpret" { INTERPRET }
  | "#rule"  { RULE }
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
  | int      { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | qvar_id  { QVAR_ID (Lexing.lexeme lexbuf) }
  | infix_cmp_id { INFIX_CMP_ID (Lexing.lexeme lexbuf) }
  | infix_fun_id { INFIX_FUN_ID (Lexing.lexeme lexbuf) }
  | id       { ID (Lexing.lexeme lexbuf) }
  | eof      { EOF }
  | _        { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }

and read_until_eol ignore_nls =
  parse
  | newline  { Lexing.new_line lexbuf; if ignore_nls then read true lexbuf else EOL }
  | eof      { EOF }
  | _        { read_until_eol ignore_nls lexbuf }

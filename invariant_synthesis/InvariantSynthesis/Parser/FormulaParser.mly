%token TRUE
%token FALSE
%token <string> ID
%token <string> INFIX_ID
%token COMMA
%token COLON
%token LEFT_PARENTHESIS
%token RIGHT_PARENTHESIS
%token FORALL
%token EXISTS
%token AND
%token OR
%token RIGHT_ARROW
%token EQUAL
%token DIFFERENT
%token NOT
%token EOF

%left COMMA
%nonassoc FORALL EXISTS
%right RIGHT_ARROW
%left OR
%left AND
%nonassoc NOT
%nonassoc EQUAL DIFFERENT INFIX_ID ID
%nonassoc COLON

%start <AST.formula option> prog
%%

prog:
  | EOF         { None }
  | v = formula { Some v }
  ;

formula:
  | TRUE
    { Const true }
  | FALSE
    { Const false }
  | LEFT_PARENTHESIS; obj = formula; RIGHT_PARENTHESIS
    { obj }
  ;

value:
  | TRUE
    { ValueConst true }
  | FALSE
    { ValueConst false }
  | LEFT_PARENTHESIS; obj = value; RIGHT_PARENTHESIS
    { obj }
  | name = ID; LEFT_PARENTHESIS; args = values; RIGHT_PARENTHESIS
    { ValueFun (name, args) }
  | arg1 = value; name = INFIX_ID; arg2 = value
    { ValueFun (name, [arg1;arg2]) }
  | name = ID
    { ValueVar name }
  ;

values:
    obj = separated_list(COMMA, value)    { obj } ;
(*
values:
  | { [] }
  | vl = rev_values { List.rev vl }
  ;
  rev_values:
  | v = value { [v] }
  | vl = rev_values; COMMA; v = value
    { v :: vl }
  ;
*)

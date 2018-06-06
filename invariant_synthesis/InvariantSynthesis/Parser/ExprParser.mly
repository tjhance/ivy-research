%{
  open AST
%}

%token BOOL TRUE FALSE
%token <string> ID
%token <string> INFIX_ID
%token SOME ELSE COMMA COLON POINT
%token LEFT_PARENTHESIS RIGHT_PARENTHESIS
%token FORALL EXISTS
%token AND OR RIGHT_ARROW
%token EQUAL DIFFERENT
%token NOT
%token EOL EOF

%right POINT
%right ELSE
%right RIGHT_ARROW
%left OR
%left AND
%nonassoc EQUAL DIFFERENT INFIX_ID
%nonassoc NOT

%start <AST.parsed_expression option> prog
%%

prog:
  | v = expression ; EOL { Some v }
  | v = expression ; EOF { Some v }
  | EOL ; p = prog { p }
  | EOF { None }
  ;

expression:
  | TRUE
    { Const (ConstBool true) }
  | FALSE
    { Const (ConstBool false) }
  | LEFT_PARENTHESIS; obj = expression; RIGHT_PARENTHESIS
    { obj }
  | e1 = expression; EQUAL; e2 = expression
    { Equal (e1, e2) }
  | e1 = expression; DIFFERENT; e2 = expression
    { Not (Equal (e1, e2)) }
  | e1 = expression; AND; e2 = expression
    { And (e1, e2) }
  | e1 = expression; OR; e2 = expression
    { Or (e1, e2) }
  | NOT; e = expression
    { Not e }
  | e1 = expression; RIGHT_ARROW; e2 = expression
    { Imply (e1, e2) }
  | FORALL; ds = decls; POINT; e = expression
    {
      List.fold_left (fun acc d -> Forall (d, acc)) e (List.rev ds)
    }
  | EXISTS; ds = decls; POINT; e = expression
    {
      List.fold_left (fun acc d -> Exists (d, acc)) e (List.rev ds)
    }
  | SOME; d = decl; POINT; e1=expression; ELSE; e2=expression
    { SomeElse (d, e1, e2) }
  | SOME; d = decl; POINT; e=expression
    { SomeElse (d, e, Const ConstVoid) }
  | name = ID; LEFT_PARENTHESIS; args = expressions; RIGHT_PARENTHESIS
    { VarFunAction (name, args) }
  | arg1 = expression; name = INFIX_ID; arg2 = expression
    { VarFunAction (name, [arg1;arg2]) }
  | name = ID
    { VarFunAction (name, []) }
  ;

expressions:
  obj = separated_list(COMMA, expression)    { obj } ;

ivy_type:
  | BOOL
    { Bool }
  | t = ID
    { Uninterpreted t }
  ;

decl:
  | name = ID ; COLON ; t = ivy_type
    { (name, t) }
  | name = ID
    { (name, Uninterpreted "") }
  ;

decls:
  obj = separated_list(COMMA, decl)    { obj } ;

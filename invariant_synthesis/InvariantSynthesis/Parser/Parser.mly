%{
  open AST
%}

%token SEMI_COLON LEFT_BRACE RIGHT_BRACE
%token ASSIGN CALL IF ASSERT ASSUME

%token BOOL TRUE FALSE
%token <string> QVAR_ID
%token <string> ID
%token <string> INFIX_ID
%token SOME ELSE COMMA COLON POINT
%token LEFT_PARENTHESIS RIGHT_PARENTHESIS
%token FORALL EXISTS
%token AND OR RIGHT_ARROW
%token EQUAL DIFFERENT
%token NOT
%token EOL EOF

%right POINT ELSE
%right RIGHT_ARROW
%left OR
%left AND
%nonassoc EQUAL DIFFERENT INFIX_ID
%nonassoc NOT

%start <AST.parsed_expression> next_expression
%start <AST.parsed_statement> next_statement
%%

(* Entry points *)

next_expression:
  list(EOL) ; v = expression ; end_expression { v } ;

end_expression:
  | EOL { }
  | EOF { }
  ;

next_statement:
  list(EOL) ; s=statement ; end_statement { s } ;

(* Statements *)

end_statement:
  | EOF { }
  | SEMI_COLON { }
  ;

statements_aux:
  s = statement ; end_statement ; list (EOL) { s } ;
statements:
  list (EOL) ; obj = list(statements_aux) { obj } ;

block_statement:
  LEFT_BRACE ; sts = statements ; RIGHT_BRACE { NewBlock ([], sts) } ;

statement:
  | { NewBlock([],[]) }
  | b = block_statement { b }
  | CALL ; e = expression { Expression e }
  | CALL ; name = ID ; ASSIGN ; e = expression { VarAssign (name, e) }
  | name = ID ; ASSIGN ; e = expression { VarAssign (name, e) }
  | name = ID ; LEFT_PARENTHESIS ; args = hole_expressions ; RIGHT_PARENTHESIS ; ASSIGN ; e = expression { GeneralFunAssign (name, args, e) }
  | IF ; e = expression ; list (EOL) ; sif = block_statement { IfElse (e, sif, NewBlock([],[])) }
  | IF ; e = expression ; list (EOL) ; sif = block_statement ; list (EOL) ;
    ELSE ; list (EOL) ; selse = block_statement { IfElse (e, sif, selse) }
  | IF ; SOME ; d = decl ; POINT ; e = expression ; list (EOL) ; sif = block_statement { IfSomeElse (d, e, sif, NewBlock([],[])) }
  | IF ; SOME ; d = decl ; POINT ; e = expression ; list (EOL) ; sif = block_statement ; list (EOL) ;
    ELSE ; list (EOL) ; selse = block_statement { IfSomeElse (d, e, sif, selse) }
  | ASSERT ; e = expression { Assert (e) }
  | ASSUME ; e = expression { Assume (e) }
  ;

decl:
  | name = ID ; COLON ; t = ivy_type
    { (name, t) }
  | name = ID
    { (name, Uninterpreted "") }
  ;
(*
decls:
  obj = separated_list(COMMA, decl) { obj } ;
*)
hole_expression:
  | e = expression { Expr e }
  | v = qvar_decl { Hole v }
  ;

hole_expressions:
  obj = separated_list(COMMA, hole_expression) { obj } ;

(* Expressions *)

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
  | FORALL; ds = qvar_decls; POINT; e = expression
    {
      List.fold_left (fun acc d -> Forall (d, acc)) e (List.rev ds)
    }
  | EXISTS; ds = qvar_decls; POINT; e = expression
    {
      List.fold_left (fun acc d -> Exists (d, acc)) e (List.rev ds)
    }
  | SOME; d = qvar_decl; POINT; e1=expression; ELSE; e2=expression
    { SomeElse (d, e1, e2) }
  | SOME; d = qvar_decl; POINT; e=expression
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

qvar_decl:
  | name = QVAR_ID ; COLON ; t = ivy_type
    { (name, t) }
  | name = QVAR_ID
    { (name, Uninterpreted "") }
  ;

qvar_decls:
  obj = separated_list(COMMA, qvar_decl)    { obj } ;

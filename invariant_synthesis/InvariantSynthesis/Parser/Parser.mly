%{
  open AST

  let type_of_decls ds =
    let aux (_,t) = t
    in List.map aux ds

  let name_of_decls ds =
    let aux (n,_) = n
    in List.map aux ds
%}

%token CONJECTURE TYPE ACTION RETURNS INDIVIDUAL FUNCTION RELATION MODULE OBJECT INSTANCE
%token AFTER BEFORE DEFINITION

%token SEMI_COLON LEFT_BRACE RIGHT_BRACE
%token ASSIGN CALL IF ASSERT ASSUME VAR

%token BOOL TRUE FALSE
%token <int> INT
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
%start <AST.parsed_element> next_element
%start <AST.parsed_element list> all_elements
%%

(* Entry points *)

next_expression:
  list(EOL) ; e = expression ; end_expression { e } ;

end_expression:
  | EOL { }
  | EOF { }
  ;

next_statement:
  list(EOL) ; s = statement ; end_statement { s } ;

next_element:
  list(EOL) ; e = element ; end_element { e } ;

all_elements_aux:
  e = element ; list (EOL) { e } ;
all_elements:
  list (EOL) ; obj = list(all_elements_aux) ; EOF { obj } ;

(* Elements *)

end_element:
  | EOL { }
  | EOF { }
  ;

elements_aux:
  e = element ; end_element ; list (EOL) { e } ;
elements:
  list (EOL) ; obj = list(elements_aux) { obj } ;

element:
  | TYPE ; name = ID { Type name }
  | INDIVIDUAL ; d = decl { Variable d }
  | FUNCTION ; name = ID ; LEFT_PARENTHESIS ; ds = qvar_decls; RIGHT_PARENTHESIS ; COLON ; t = ivy_type { Function(name, type_of_decls(ds), t, false) }
  | FUNCTION ; LEFT_PARENTHESIS ; d1 = qvar_decl ; name = INFIX_ID ; d2 = qvar_decl ; RIGHT_PARENTHESIS ; COLON ; t = ivy_type { Function(name, type_of_decls([d1;d2]), t, true) }
  | RELATION ; name = ID ; LEFT_PARENTHESIS ; ds = qvar_decls; RIGHT_PARENTHESIS { Function(name, type_of_decls(ds), Bool, false) }
  | RELATION ; LEFT_PARENTHESIS ; d1 = qvar_decl ; name = INFIX_ID ; d2 = qvar_decl ; RIGHT_PARENTHESIS { Function(name, type_of_decls([d1;d2]), Bool, true) }
  | DEFINITION ; name = ID ; args = action_args ; EQUAL ; e = expression { Macro (name, args, e) }
  | ACTION ; name = ID ; args = action_args ; ret = action_ret { AbstractAction (name, args, ret) }
  | ACTION ; name = ID ; args = action_args ; ret = action_ret ; EQUAL ; list(EOL) ; st = block_statement { Action (name, args, ret, st) }
  | AFTER ; name = ID ; list(EOL) ; st = block_statement { After (name, st) }
  | BEFORE ; name = ID ; list(EOL) ; st = block_statement { Before (name, st) }
  | CONJECTURE ; e = expression { Conjecture e }
  | MODULE ; name = ID ; args = module_args ; EQUAL ; list(EOL) ; els = block_of_elements { Module (name, args, els) }
  | OBJECT ; name = ID ; EQUAL ; list(EOL) ; els = block_of_elements { Object (name, els) }
  | INSTANCE ; name = ID ; COLON ; mod_name = ID ; args = module_args { ObjectFromModule (name, mod_name, args) }
  ;

block_of_elements:
  LEFT_BRACE ; es = elements ; RIGHT_BRACE { es } ;

module_args:
  | LEFT_PARENTHESIS ; ds = decls; RIGHT_PARENTHESIS { name_of_decls ds }
  | { [] }
  ;

action_args:
  | LEFT_PARENTHESIS ; ds = decls; RIGHT_PARENTHESIS { ds }
  | { [] }
  ;

action_ret:
  | RETURNS ; LEFT_PARENTHESIS ; d = decl; RIGHT_PARENTHESIS { d }
  | { ("", Void) }
  ;

decls:
  obj = separated_list(COMMA, decl) { obj } ;

(* Statements *)

end_statement:
  | SEMI_COLON { }
  ;

statements_aux:
  s = statement ; end_statement ; list (EOL) { s } ;
statements:
  list (EOL) ; obj = list(statements_aux) { obj } ;

block_statement:
  LEFT_BRACE ; sts = statements ; RIGHT_BRACE { NewBlock sts } ;

statement:
  | { NewBlock([]) }
  | b = block_statement { b }
  | VAR ; d = decl { NewVar (d, None) }
  | VAR ; d = decl ; ASSIGN ; e = expression { NewVar (d, Some e) }
  | CALL ; e = expression { Expression e }
  | CALL ; name = ID ; ASSIGN ; e = expression { VarAssign (name, e) }
  | name = ID ; ASSIGN ; e = expression { VarAssign (name, e) }
  | name = ID ; LEFT_PARENTHESIS ; args = (*hole_*)expressions ; RIGHT_PARENTHESIS ; ASSIGN ; e = expression { GeneralFunAssign (name, args, e) }
  | IF ; e = expression ; list (EOL) ; sif = block_statement { IfElse (e, sif, NewBlock([])) }
  | IF ; e = expression ; list (EOL) ; sif = block_statement ; list (EOL) ;
    ELSE ; list (EOL) ; selse = block_statement { IfElse (e, sif, selse) }
  | IF ; SOME ; d = decl ; POINT ; e = expression ; list (EOL) ; sif = block_statement { IfSomeElse (d, e, sif, NewBlock([])) }
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
hole_expression:
  | e = expression { Expr e }
  | v = qvar_decl { Hole v }
  ;

hole_expressions:
  obj = separated_list(COMMA, hole_expression) { obj } ;
*)

(* Expressions *)

expression:
  | TRUE
    { Const (ConstBool true) }
  | FALSE
    { Const (ConstBool false) }
  | i = INT
    { Const (ConstInt i) }
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
  | d = qvar_decl
    { QVar d }
  ;

expressions:
  obj = separated_list(COMMA, expression) { obj } ;

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
  obj = separated_list(COMMA, qvar_decl) { obj } ;

%{
  open AST

  let type_of_decls ds =
    let aux (_,t) = t
    in List.map aux ds

%}

%token CONJECTURE TYPE ACTION RETURNS INDIVIDUAL FUNCTION RELATION MODULE OBJECT INSTANCE
%token AFTER BEFORE AXIOM DEFINITION INSTANTIATE IMPLEMENT INTERPRET EXPORT

%token SEMI_COLON LEFT_BRACE RIGHT_BRACE
%token ASSIGN CALL IF VAR ASSERT ASSUME REQUIRE ENSURE

%token BOOL TRUE FALSE
%token STAR
%token <int> INT
%token <string> QVAR_ID
%token <string> ID
%token <string> INFIX_CMP_ID INFIX_FUN_ID
%token SOME ELSE COMMA COLON POINT
%token LEFT_PARENTHESIS RIGHT_PARENTHESIS
%token FORALL EXISTS
%token AND OR RIGHT_ARROW
%token EQUAL DIFFERENT
%token NOT
%token EOL EOF

%right POINT IF ELSE
%right RIGHT_ARROW
%left OR
%left AND
%nonassoc EQUAL DIFFERENT INFIX_CMP_ID
%nonassoc INFIX_FUN_ID
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
  | TYPE ; name = ID { Type (name, None) }
  | TYPE ; name = ID ; EQUAL ; LEFT_BRACE ; ds = enum_decls ; RIGHT_BRACE { Type (name, Some ds) }
  | INTERPRET ; t = ID ; RIGHT_ARROW ; str = ID { Interpret (t, str) }
  | INDIVIDUAL ; d = decl { Variable d }
  | FUNCTION ; name = ID ; LEFT_PARENTHESIS ; ds = qvar_decls; RIGHT_PARENTHESIS ; COLON ; t = ivy_type { Function(name, type_of_decls(ds), t, false) }
  | FUNCTION ; LEFT_PARENTHESIS ; d1 = qvar_decl ; name = INFIX_FUN_ID ; d2 = qvar_decl ; RIGHT_PARENTHESIS ; COLON ; t = ivy_type { Function(name, type_of_decls([d1;d2]), t, true) }
  | RELATION ; name = ID ; LEFT_PARENTHESIS ; ds = qvar_decls; RIGHT_PARENTHESIS { Function(name, type_of_decls(ds), Bool, false) }
  | RELATION ; LEFT_PARENTHESIS ; d1 = qvar_decl ; name = INFIX_CMP_ID ; d2 = qvar_decl ; RIGHT_PARENTHESIS { Function(name, type_of_decls([d1;d2]), Bool, true) }
  | DEFINITION ; name = ID ; args = action_args ; EQUAL ; e = expression { Macro (name, args, e, false) }
  | DEFINITION ; LEFT_PARENTHESIS ; d1 = decl ; name = INFIX_FUN_ID ; d2 = decl ; RIGHT_PARENTHESIS ; EQUAL ; e = expression { Macro (name, [d1;d2], e, true) }
  | DEFINITION ; name = ID ; LEFT_PARENTHESIS ; args = qvar_decls_ne ; RIGHT_PARENTHESIS ; EQUAL ; e = expression {
    let args = List.map (fun arg -> QVar arg) args in
    Axiom (Equal (VarFunMacroAction (name, args), e)) }
  | AXIOM ; e = expression { Axiom e }
  | ACTION ; name = ID ; args = action_args ; ret = action_ret { AbstractAction (name, args, ret) }
  | ACTION ; name = ID ; args = action_args ; ret = action_ret ; EQUAL ; list(EOL) ; st = block_statement { Action (name, args, ret, st) }
  | IMPLEMENT ; name = ID ; list(EOL) ; st = block_statement { Implement (name, st) }
  | AFTER ; name = ID ; list(EOL) ; st = block_statement { After (name, st) }
  | BEFORE ; name = ID ; list(EOL) ; st = block_statement { Before (name, st) }
  | CONJECTURE ; e = expression { Conjecture e }
  | MODULE ; name = ID ; args = module_args ; EQUAL ; list(EOL) ; els = block_of_elements { Module (name, args, els) }
  | OBJECT ; name = ID ; EQUAL ; list(EOL) ; els = block_of_elements { Object (name, els) }
  | INSTANCE ; name = ID ; COLON ; mod_name = ID ; args = module_args_with_infix { ObjectFromModule (name, mod_name, args) }
  | INSTANTIATE ; mod_name = ID ; args = module_args_with_infix { ObjectFromModule ("", mod_name, args) }
  | EXPORT ; name = ID { Export name }
  ;

qvar_decls_ne:
  obj = separated_nonempty_list(COMMA, qvar_decl) { obj } ;

block_of_elements:
  LEFT_BRACE ; es = elements ; RIGHT_BRACE { es } ;

module_args_with_infix:
  | LEFT_PARENTHESIS ; ds = module_decls_with_infix; RIGHT_PARENTHESIS { ds }
  | { [] }
  ;

module_args:
  | LEFT_PARENTHESIS ; ds = module_decls; RIGHT_PARENTHESIS { ds }
  | { [] }
  ;

action_args:
  | LEFT_PARENTHESIS ; ds = decls; RIGHT_PARENTHESIS { ds }
  | { [] }
  ;

action_ret:
  | RETURNS ; LEFT_PARENTHESIS ; d = decl; RIGHT_PARENTHESIS { Some d }
  | { None }
  ;

enum_decls:
  obj = separated_list(COMMA, ID) { obj } ;

module_decls:
  obj = separated_list(COMMA, ID) { obj } ;

module_decls_with_infix:
  obj = separated_list(COMMA, module_decl_with_infix) { obj } ;

module_decl_with_infix:
  | name = ID { name }
  | name = infix_id { name }
  ;

infix_id:
  | n = INFIX_CMP_ID { n }
  | n = INFIX_FUN_ID { n }
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
  | CALL ; name = ID ; ASSIGN ; e = expression { VarFunAssign (name, [], e) }
  | name = ID ; ASSIGN ; e = expression { VarFunAssign (name, [], e) }
  | name = ID ; LEFT_PARENTHESIS ; args = (*hole_*)expressions ; RIGHT_PARENTHESIS ; ASSIGN ; e = expression { VarFunAssign (name, args, e) }
  | IF ; e = expression ; list (EOL) ; sif = block_statement { IfElse (e, sif, NewBlock([])) }
  | IF ; e = expression ; list (EOL) ; sif = block_statement ; list (EOL) ;
    ELSE ; list (EOL) ; selse = block_statement { IfElse (e, sif, selse) }
  | IF ; SOME ; d = decl ; POINT ; e = expression ; list (EOL) ; sif = block_statement { IfSomeElse (d, e, sif, NewBlock([])) }
  | IF ; SOME ; d = decl ; POINT ; e = expression ; list (EOL) ; sif = block_statement ; list (EOL) ;
    ELSE ; list (EOL) ; selse = block_statement { IfSomeElse (d, e, sif, selse) }
  | ASSERT ; e = expression { Assert (e) }
  | ASSUME ; e = expression { Assume (e) }
  | REQUIRE ; e = expression { Require (e) }
  | ENSURE ; e = expression { Ensure (e) }
  ;

decl:
  | name = ID ; COLON ; t = ivy_type
    { (name, t) }
  | name = ID
    { (name, Unknown) }
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
  | STAR
    { Star }
  | i = INT
    { Const (ConstInt ("", i)) }
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
  | eif = expression; IF ; e = expression ; ELSE ; eelse = expression
    { ExprIfElse (e, eif, eelse) }
  | FORALL; ds = qvar_decls; POINT; e = expression
    {
      List.fold_left (fun acc d -> Forall (d, acc)) e (List.rev ds)
    }
  | EXISTS; ds = qvar_decls; POINT; e = expression
    {
      List.fold_left (fun acc d -> Exists (d, acc)) e (List.rev ds)
    }
  | SOME; d = qvar_decl; POINT; e1=expression; ELSE; e2=expression
    { SomeElse (d, e1, Some e2) }
  | SOME; d = qvar_decl; POINT; e=expression
    { SomeElse (d, e, None) }
  | name = ID; LEFT_PARENTHESIS; args = expressions; RIGHT_PARENTHESIS
    { VarFunMacroAction (name, args) }
  | arg1 = expression; name = INFIX_CMP_ID; arg2 = expression
    { VarFunMacroAction (name, [arg1;arg2]) }
  | arg1 = expression; name = INFIX_FUN_ID; arg2 = expression
    { VarFunMacroAction (name, [arg1;arg2]) }
  | name = ID
    { VarFunMacroAction (name, []) }
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
    { (name, Unknown) }
  ;

qvar_decls:
  obj = separated_list(COMMA, qvar_decl) { obj } ;

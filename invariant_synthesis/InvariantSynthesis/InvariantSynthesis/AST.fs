module AST

    (* A VERY BASIC AST FOR IVY *)

    // TODO: Recode Interpreter/Synthesis with a trace system
    // TODO: Adapt the Interpreter/Synthesis in order to be able to also analyze assertion fails

    type Type =
        | Void
        | Bool
        | Uninterpreted of string

    type TypeDecl = { Name: string }
    type FunDecl = { Name: string; Input: List<Type>; Output: Type }
    type VarDecl = { Name: string; Type: Type }

    type ConstValue =
        | ConstVoid // Only used for actions that return nothing (or sometimes for errors)
        | ConstBool of bool // Type name, value
        | ConstInt of string * int // Type name, value

    (* No side effects *)
    type Value =
        | ValueConst of ConstValue
        | ValueVar of string
        | ValueFun of string * List<Value>
        | ValueEqual of Value * Value
        | ValueOr of Value * Value
        | ValueAnd of Value * Value
        | ValueNot of Value
        | ValueSomeElse of VarDecl * Formula * Value

    and Formula =
        | Const of bool
        | Equal of Value * Value
        | Or of Formula * Formula
        | And of Formula * Formula
        | Not of Formula
        | Forall of VarDecl * Formula
        | Exists of VarDecl * Formula

    (* With side effects *)
    type Expression =
        | ExprConst of ConstValue
        | ExprVar of string
        | ExprFun of string * List<Expression>
        | ExprAction of string * List<Expression>
        | ExprEqual of Expression * Expression
        | ExprOr of Expression * Expression
        | ExprAnd of Expression * Expression
        | ExprNot of Expression
        | ExprSomeElse of VarDecl * Formula * Expression

    type HoleExpression =
        | Hole of VarDecl
        | Expr of Expression

    type Statement =
        | NewBlock of List<VarDecl> * List<Statement>
        | Expression of Expression
        | VarAssign of string * Expression
        | FunAssign of string * List<Expression> * Expression
        | ForallFunAssign of string * List<HoleExpression> * Value
        | IfElse of Expression * Statement * Statement
        | IfSomeElse of VarDecl * Formula * Statement * Statement
        | Assert of Formula
    // TODO: Implement ForallFunAssign
    (*
    fun (ei,Xi) = V(Xi)

    2 cases:

    Nothing marked:
    restrict ei as usual

    Some values marked in m or um:
    restrict all ei

    Then:

    Foreach value marked in m:
    remove mark for value in m
    restrict V(Xi) for corresponding values of Xi (no uvar)

    Foreach value marked in um:
    remove mark for value in um
    restrict V(Xi) for corresponding values of Xi (with X in uvar)
    *)

    type ActionDecl = { Name: string; Args: List<VarDecl>; Output: VarDecl; Content: Statement }
    type ModuleDecl = { Name: string; Types: List<TypeDecl>; Funs: List<FunDecl>; Vars: List<VarDecl>; Actions: List<ActionDecl>; Invariants: List<Formula> }


    let find_relation<'a,'b> (m:ModuleDecl) str =
        List.find (fun (decl:FunDecl) -> decl.Name = str) m.Funs
    
    let find_variable<'a,'b> (m:ModuleDecl) str =
        List.find (fun (decl:VarDecl) -> decl.Name = str) m.Vars

    let find_action<'a,'b> (m:ModuleDecl) str =
        List.find (fun (decl:ActionDecl) -> decl.Name = str) m.Actions

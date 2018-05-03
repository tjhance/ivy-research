namespace AST

    (* A VERY BASIC AST FOR IVY *)

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

    (* No side effects *)
    type Formula =
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

    type Statement =
        | NewBlock of List<VarDecl> * List<Statement>
        | Expression of Expression
        | VarAssign of string * Expression
        | FunAssign of string * List<Expression> * Expression
        | IfSomeElse of VarDecl * Formula * Statement * Statement
        | Assert of Formula

    type AbstractModifier = { v: VarDecl -> ConstValue -> ConstValue ; f: FunDecl -> List<ConstValue> -> ConstValue -> ConstValue }

    type ActionDecl = { Name: string; Args: List<VarDecl>; Output: VarDecl; Content: Statement }
    type AbstractActionDecl = { Name: string; Args: List<VarDecl>; Output: VarDecl; Effect: AbstractModifier; Assume: List<Formula>; Assert: List<Formula> }
    type ModuleDecl = { Name: string; Types: List<TypeDecl>; Funs: List<FunDecl>; Vars: List<VarDecl>; Actions: List<ActionDecl>; Invariants: List<Formula> }

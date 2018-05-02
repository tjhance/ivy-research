namespace IVY

    (* A VERY BASIC AST FOR IVY *)
    type Type =
        | Void
        | Bool
        | Custom of string

    type TypeDecl = { Name: string }
    type FunDecl = { Name: string; Input: List<Type>; Output: Type }
    type VarDecl = { Name: string; Type: Type }

    type ConstValue =
        | ConstVoid // Only used for actions that return nothing
        | ConstInt of int
        | ConstBool of bool

    (* No side effects *)
    type Value =
        | ConstValue of ConstValue
        | Var of string
        | Fun of string * List<Value>

    (* No side effects *)
    type Formula =
        | Const of bool
        | Equal of Value * Value
        //| StrictlySmaller of Value * Value // Can be considered as a regular relation
        | Or of Formula * Formula
        | And of Formula * Formula
        | Not of Formula
        | Forall of VarDecl * Formula
        | Exists of VarDecl * Formula
    
    (* With side effects *)
    type Expression =
        | Value of Value
        | Action of string * List<Expression>

    type Statement =
        | NewBlock of List<VarDecl> * List<Statement>
        | VarAssign of string * Expression
        | FunAssign of string * List<Value> * Expression
        | IfSomeElse of VarDecl * Formula * Statement * Statement
        | Assume of Formula
        | Assert of Formula

    type ActionDecl = { Name: string; Args: List<VarDecl>; Output: VarDecl; Content: Statement }
    type ModuleDecl = { Name: string; Types: List<TypeDecl>; Funs: List<FunDecl>; Vars: List<VarDecl>; Actions: List<ActionDecl>; Invariants: List<Formula> }

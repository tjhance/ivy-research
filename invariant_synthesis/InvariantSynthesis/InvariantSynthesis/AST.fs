namespace AST

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
        | ConstBool of bool
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
      //| StrictlySmaller of Value * Value // Can be considered as a regular relation
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
        | ExprNot of Expression * Expression

    type Statement =
        | NewBlock of List<VarDecl> * List<Statement>
        | VarAssign of string * Expression
        | FunAssign of string * List<Value> * Expression
        | IfSomeElse of VarDecl * Formula * Statement * Statement
        | Assume of Formula
        | Assert of Formula

    type ActionDecl = { Name: string; Args: List<VarDecl>; Output: VarDecl; Content: Statement }
    type ModuleDecl = { Name: string; Types: List<TypeDecl>; Funs: List<FunDecl>; Vars: List<VarDecl>; Actions: List<ActionDecl>; Invariants: List<Formula> }

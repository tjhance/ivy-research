namespace AST

(* A VERY BASIC AST FOR IVY *)

type TypeDecl = { Name: string }
type FunDecl = { Name: string; Input: List<string>; Output: string }
type RelDecl = { Name: string; Input: List<string> }
type VarDecl = { Name: string; Type: string }

type Value =
    | ConstInt of int
    | Var of string
    | Fun of string * List<Value>

type Formula =
    | ConstBool of bool
    | Equal of Value * Value
    //| StrictlySmaller of Value * Value // Can be considered as a regular expression
    | Rel of string * List<Value>
    | Or of Formula * Formula
    | And of Formula * Formula
    | Not of Formula
    | Forall of VarDecl * Formula
    | Exists of VarDecl * Formula

type Expression =
    | Value of Value
    | Formula of Formula
    | Action of string * List<Expression>

type LeftValue =
    | Var of string
    | Fun of string * List<Value>
    | Rel of string * List<Value>

type Statement =
    | NewBlock of List<VarDecl> * List<Statement>
    | Assign of LeftValue * Expression
    | IfSomeElse of VarDecl * Formula * Statement * Statement
    | Assume of Formula
    | Assert of Formula

type ActionDecl = { Name: string; Args: List<VarDecl>; Output: VarDecl; Content: Statement }
type ModuleDecl = { Name: string; Types: List<TypeDecl>; Funs: List<FunDecl>; Rels: List<RelDecl>; Vars: List<VarDecl>; Actions: List<ActionDecl>; Invariants: List<Formula> }

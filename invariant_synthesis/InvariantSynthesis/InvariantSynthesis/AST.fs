module AST

open System

    (* A VERY BASIC AST FOR IVY *)

    // TODO: Recode Interpreter/Synthesis with a trace system
    // TODO: Adapt the Interpreter/Synthesis in order to be able to also analyze assertion fails
    // TODO: Parse Ivy code
    // TODO: implement 2 steps synthesis (with user help)
    // TODO: delete flag system and use implications instead
    // TODO: Use model checking tool to know whether 2steps synthesis is needed

    type Type =
        | Void
        | Bool
        | Uninterpreted of string

    type RepresentationFlags = Infix
    type RepresentationInfos = { DisplayName: string option; Flags: Set<RepresentationFlags> }

    type RelationFlags =
        | Reflexive
        | Transitive
        | Symetric
        | AntiSymetric

    type TypeDecl = { Name: string }
    type FunDecl = { Name: string; Input: List<Type>; Output: Type;
        Representation: RepresentationInfos; Flags: Set<RelationFlags>; NegFlags: Set<RelationFlags> }
    type VarDecl = { Name: string; Type: Type; Representation: RepresentationInfos }

    type PatternValue =
        | PatternConst of bool
        | PatternVar of string

    type Pattern =
        | VarPattern of PatternValue * string
        | RelPattern of PatternValue * string * List<PatternValue>
        | ValueDiffPattern of Type * PatternValue * PatternValue

    type ImplicationRule = Set<Pattern> * Set<Pattern>

    let default_representation : RepresentationInfos = { DisplayName = None; Flags = Set.empty }

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
        | ExprSomeElse of VarDecl * Formula * Value

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

    type ActionDecl = { Name: string; Args: List<VarDecl>; Output: VarDecl; Content: Statement }
    type ModuleDecl =
        { Name: string; Types: List<TypeDecl>; Funs: List<FunDecl>; Vars: List<VarDecl>;
            Actions: List<ActionDecl>; Invariants: List<Formula>; Implications: List<ImplicationRule> }


    let type_of_const_value cv =
        match cv with
        | ConstVoid -> Void
        | ConstBool _ -> Bool
        | ConstInt (s,_) -> Uninterpreted s

    let find_relation<'a,'b> (m:ModuleDecl) str =
        List.find (fun (decl:FunDecl) -> decl.Name = str) m.Funs
    
    let find_variable<'a,'b> (m:ModuleDecl) str =
        List.find (fun (decl:VarDecl) -> decl.Name = str) m.Vars

    let find_action<'a,'b> (m:ModuleDecl) str =
        List.find (fun (decl:ActionDecl) -> decl.Name = str) m.Actions

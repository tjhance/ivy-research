module AST

    (* A VERY BASIC AST FOR IVY *)

    // TODO: "For" loops
    // TODO: "if some" with multiple var decls
    // TODO: Allow multiple return values for actions.
    // If used in an expression, returns ConstVoid.
    // If used in a "call" statement, assign each value.
    // TODO: Handle functions with an object as return value (case of instance a(X):b(Y))
    // For that, we can consider those functions an instance of the corresponding module,
    // with an additionals first parameters for every var/fun/action/etc (that corresponds the parameters of the initial function)
    // TODO: Axiom, isolate, inductive, export, extract, interpret, property...

    // TODO: Parse Ivy code

    // TODO: Use model checking tool to know whether 2steps synthesis is needed?
    // TODO: OR Use an automated method: computing weakest precondition (wp) and finding
    // a finite model for (wp AND NOT new_strong_invariant). Having the same args
    // for the action should also be imposed in order to have a comparable environment.

    type Type =
        | Void
        | Bool
        | Uninterpreted of string

    type RepresentationFlags = Infix
    type RepresentationInfos = { DisplayName: string option; Flags: Set<RepresentationFlags> }

    type TypeDecl = { Name: string }
    type FunDecl = { Name: string; Input: List<Type>; Output: Type; Representation: RepresentationInfos }
    type VarDecl = { Name: string; Type: Type; Representation: RepresentationInfos }

    type PatternValue =
        | PatternConst of bool
        | PatternVar of string

    type Pattern =
        | VarPattern of PatternValue * string
        | RelPattern of PatternValue * string * List<PatternValue>
        | ValueDiffPattern of string * PatternValue * PatternValue

    type ImplicationRule = Set<Pattern> * Set<Pattern>

    let default_representation : RepresentationInfos = { DisplayName = None; Flags = Set.empty }

    type ConstValue =
        | ConstVoid // Only used for actions that return nothing
        | ConstBool of bool // Type name, value
        | ConstInt of string * int // Type name, value

    (* No side effects *)
    type Value =
        | ValueConst of ConstValue
        | ValueVar of string
        | ValueFun of string * List<Value>
        | ValueMacro of string * List<Value>
        | ValueEqual of Value * Value
        | ValueOr of Value * Value
        | ValueAnd of Value * Value
        | ValueNot of Value
        | ValueSomeElse of VarDecl * Value * Value
        | ValueForall of VarDecl * Value
        | ValueExists of VarDecl * Value
        | ValueImply of Value * Value

    (* With side effects *)
    type Expression =
        | ExprConst of ConstValue
        | ExprVar of string
        | ExprFun of string * List<Expression>
        | ExprMacro of string * List<Value>
        | ExprAction of string * List<Expression>
        | ExprEqual of Expression * Expression
        | ExprOr of Expression * Expression
        | ExprAnd of Expression * Expression
        | ExprNot of Expression
        | ExprSomeElse of VarDecl * Value * Value
        | ExprForall of VarDecl * Value
        | ExprExists of VarDecl * Value
        | ExprImply of Expression * Expression

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
        | IfSomeElse of VarDecl * Value * Statement * Statement
        | Assert of Value

    type ActionDecl = { Name: string; Args: List<VarDecl>; Output: VarDecl; Content: Statement }

    type MacroDecl = { Name: string; Args: List<VarDecl>; Output: Type; Value: Value }

    type ModuleDecl =
        { Name: string; Types: List<TypeDecl>; Funs: List<FunDecl>; Vars: List<VarDecl>;
            Actions: List<ActionDecl>; Macros: List<MacroDecl>; Invariants: List<Value>; Implications: List<ImplicationRule> }


    let empty_module name =
        {
            Name=name;
            Types=[];
            Funs=[];
            Vars=[];
            Actions=[];
            Macros=[];
            Invariants=[];
            Implications=[];
        }

    let type_of_const_value cv =
        match cv with
        | ConstVoid -> Void
        | ConstBool _ -> Bool
        | ConstInt (s,_) -> Uninterpreted s

    let find_function (m:ModuleDecl) str =
        List.find (fun (decl:FunDecl) -> decl.Name = str) m.Funs
    
    let find_variable (m:ModuleDecl) str =
        List.find (fun (decl:VarDecl) -> decl.Name = str) m.Vars

    let find_action (m:ModuleDecl) str =
        List.find (fun (decl:ActionDecl) -> decl.Name = str) m.Actions

    let find_macro (m:ModuleDecl) str =
        List.find (fun (decl:MacroDecl) -> decl.Name = str) m.Macros

    let default_var_decl name t =
        { VarDecl.Name = name ; VarDecl.Type = t ; VarDecl.Representation = default_representation }

    let rec map_vars_in_value v dico =
        match v with
        | ValueConst c -> ValueConst c
        | ValueVar str ->
            if Map.containsKey str dico
            then Map.find str dico
            else ValueVar str
        | ValueFun (str, vs) ->
            ValueFun (str, List.map (fun v -> map_vars_in_value v dico) vs)
        | ValueMacro (str, vs) ->
            ValueMacro (str, List.map (fun v -> map_vars_in_value v dico) vs)
        | ValueEqual (v1, v2) ->
            ValueEqual (map_vars_in_value v1 dico, map_vars_in_value v2 dico)
        | ValueOr (v1, v2) ->
            ValueOr (map_vars_in_value v1 dico, map_vars_in_value v2 dico)
        | ValueAnd (v1, v2) ->
            ValueAnd (map_vars_in_value v1 dico, map_vars_in_value v2 dico)
        | ValueNot v ->
            ValueNot (map_vars_in_value v dico)
        | ValueSomeElse (d, v1, v2) ->
            ValueSomeElse (d, map_vars_in_value v1 dico, map_vars_in_value v2 dico)
        | ValueForall (d,v) ->
            ValueForall (d, map_vars_in_value v dico)
        | ValueExists (d,v) ->
            ValueExists (d, map_vars_in_value v dico)
        | ValueImply (v1, v2) ->
            ValueImply (map_vars_in_value v1 dico, map_vars_in_value v2 dico)

    let rec expr_to_value expr =
        match expr with
        | ExprConst c -> ValueConst c
        | ExprVar v -> ValueVar v
        | ExprFun (str,args) -> ValueFun (str, List.map expr_to_value args)
        | ExprMacro (str, args) -> ValueMacro (str, args)
        | ExprAction _ -> failwith "Value expected, side-effects found!"
        | ExprEqual (e1, e2) -> ValueEqual (expr_to_value e1, expr_to_value e2)
        | ExprOr (e1, e2) -> ValueOr (expr_to_value e1, expr_to_value e2)
        | ExprAnd (e1, e2) -> ValueAnd (expr_to_value e1, expr_to_value e2)
        | ExprNot e -> ValueNot (expr_to_value e)
        | ExprSomeElse (d, v1, v2) -> ValueSomeElse (d, v1, v2)
        | ExprForall (d,v) -> ValueForall (d,v)
        | ExprExists (d,v) -> ValueExists (d,v)
        | ExprImply (e1, e2) -> ValueImply (expr_to_value e1, expr_to_value e2)

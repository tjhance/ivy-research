module AST

    (* A VERY BASIC AST FOR IVY *)

    // TODO: Improvement of the synthesis: for fun marks in um, remember which parameters are universally quantified (this info can be used in FunAssign analysis)
    // TODO: Find a way to add implication rules when parsing
    // TODO: treat differently 'assume', 'assert', 'require' and 'ensure'

    // TODO: Enumerated types
    // TODO: "For" loops
    // TODO: "if some" with multiple var decls
    // TODO: Allow multiple return values for actions.
    // If used in an expression, returns ConstVoid.
    // If used in a "call" statement, assign each value.
    // TODO: Handle functions with an object as return value (case of instance a(X):b(Y))
    // For that, we can consider those functions an instance of the corresponding module,
    // with an additionals first parameters for every var/fun/action/etc (that corresponds the parameters of the initial function)
    // TODO: non-deterministic stuff (like 'var a = *')
    // TODO: Axiom, isolate, inductive, export, extract, interpret, property...
    // TODO: Infer types for macro args (currently, type annotations is required)

    // TODO: Use an automated method: computing weakest precondition (wp) and finding a finite model for (wp AND NOT new_strong_invariant).

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
        | ValueInterpreted of string * List<Value>

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
        | ExprInterpreted of string * List<Expression>

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

    type MacroDecl = { Name: string; Args: List<VarDecl>; Output: Type; Value: Value ; Representation: RepresentationInfos }

    [<NoEquality;NoComparison>]
    type InterpretedActionDecl<'a,'b> = { Name: string; Args: List<Type>; Output: Type; Effect: 'a -> 'b -> List<ConstValue> -> ConstValue ; Representation: RepresentationInfos }

    [<NoEquality;NoComparison>]
    type ModuleDecl<'a,'b> =
        { Name: string; Types: List<TypeDecl>; Funs: List<FunDecl>; Vars: List<VarDecl>; InterpretedActions: List<InterpretedActionDecl<'a,'b>>;
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
            InterpretedActions=[];
        }

    let default_var_decl name t =
        { VarDecl.Name = name ; VarDecl.Type = t ; VarDecl.Representation = default_representation }

    // Var names functions

    let action_variant_char = ':'

    let variant_action_name name variant =
        if variant = ""
        then name
        else sprintf "%s%c%s" name action_variant_char variant

    let local_var_prefix = "$" // We assign a prefix to non-global vars in order to avoid bugs due to vars scope

    let impossible_var_prefix = "$$"

    let void_return_decl = default_var_decl impossible_var_prefix Void

    let impossible_name name =
        sprintf "%s%s" impossible_var_prefix name

    let local_name name =
        sprintf "%s%s" local_var_prefix name

    // Utility functions

    let find_function (m:ModuleDecl<'a,'b>) str =
        List.find (fun (decl:FunDecl) -> decl.Name = str) m.Funs
    
    let find_variable (m:ModuleDecl<'a,'b>) str =
        List.find (fun (decl:VarDecl) -> decl.Name = str) m.Vars

    let rec find_action (m:ModuleDecl<'a,'b>) str add_variants =
        let action = List.find (fun (decl:ActionDecl) -> decl.Name = str) m.Actions
        if add_variants
        then
            let action =
                try
                    let before = find_action m (variant_action_name str "before") add_variants
                    { action with Content=NewBlock([],[before.Content;action.Content]) }
                with :? System.Collections.Generic.KeyNotFoundException -> action
            let action =
                try
                    let after = find_action m (variant_action_name str "after") add_variants
                    { action with Content=NewBlock([],[action.Content;after.Content]) }
                with :? System.Collections.Generic.KeyNotFoundException -> action
            action
        else
            action

    let find_interpreted_action (m:ModuleDecl<'a,'b>) str =
        List.find (fun (decl:InterpretedActionDecl<'a,'b>) -> decl.Name = str) m.InterpretedActions

    let find_macro (m:ModuleDecl<'a,'b>) str =
        List.find (fun (decl:MacroDecl) -> decl.Name = str) m.Macros

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
        | ValueInterpreted (str, vs) ->
            ValueInterpreted (str, List.map (fun v -> map_vars_in_value v dico) vs)

    let rec expr_to_value expr =
        match expr with
        | ExprConst c -> ValueConst c
        | ExprVar v -> ValueVar v
        | ExprFun (str,args) -> ValueFun (str, List.map expr_to_value args)
        | ExprMacro (str, args) -> ValueMacro (str, args)
        | ExprAction _ -> failwith "Value expected, action found!"
        | ExprEqual (e1, e2) -> ValueEqual (expr_to_value e1, expr_to_value e2)
        | ExprOr (e1, e2) -> ValueOr (expr_to_value e1, expr_to_value e2)
        | ExprAnd (e1, e2) -> ValueAnd (expr_to_value e1, expr_to_value e2)
        | ExprNot e -> ValueNot (expr_to_value e)
        | ExprSomeElse (d, v1, v2) -> ValueSomeElse (d, v1, v2)
        | ExprForall (d,v) -> ValueForall (d,v)
        | ExprExists (d,v) -> ValueExists (d,v)
        | ExprImply (e1, e2) -> ValueImply (expr_to_value e1, expr_to_value e2)
        | ExprInterpreted (str, args) -> ValueInterpreted (str, List.map expr_to_value args)

    let expand_macro (macro:MacroDecl) args =
        let dico = List.fold2 (fun acc (d:VarDecl) v -> Map.add d.Name v acc) Map.empty macro.Args args
        map_vars_in_value (macro.Value) dico

    // Functions on types

    let type_of_const_value cv =
        match cv with
        | ConstVoid -> Void
        | ConstBool _ -> Bool
        | ConstInt (s,_) -> Uninterpreted s

    // Note: In synthesis.fs, operations like Set.contains or Set.remove doesn't take value_equal into account.
    let value_equal _ v1 v2 = v1=v2

    let type_equal t1 t2 = t1=t2

    let rec type_of_value<'a,'b> (m:ModuleDecl<'a,'b>) value dico =
        match value with
        | ValueConst cv -> type_of_const_value cv
        | ValueVar v ->
            match Map.tryFind v dico with
            | None -> (find_variable m v).Type
            | Some t -> t
        | ValueFun (f,_) -> (find_function m f).Output
        | ValueMacro (str,_) -> (find_macro m str).Output
        | ValueEqual _ | ValueOr _ | ValueAnd _ | ValueNot _ | ValueImply _
        | ValueForall _ | ValueExists _ -> Bool
        | ValueSomeElse (_,_,v) -> type_of_value m v dico
        | ValueInterpreted (str, _) -> (find_interpreted_action m str).Output

    let type_of_expr<'a,'b> (m:ModuleDecl<'a,'b>) expr dico =
        match expr with
        | ExprConst cv -> type_of_const_value cv
        | ExprVar v ->
            match Map.tryFind v dico with
            | None -> (find_variable m v).Type
            | Some t -> t
        | ExprFun (f,_) -> (find_function m f).Output
        | ExprMacro (str,_) -> (find_macro m str).Output
        | ExprAction (str, _) -> (find_action m str false).Output.Type
        | ExprEqual _ | ExprOr _ | ExprAnd _ | ExprNot _ | ExprImply _
        | ExprForall _ | ExprExists _ -> Bool
        | ExprSomeElse (_,_,v) -> type_of_value m v dico
        | ExprInterpreted (str, _) -> (find_interpreted_action m str).Output

    let type_of_hole_expr<'a,'b> (m:ModuleDecl<'a,'b>) hexpr dico =
        match hexpr with
        | Expr e -> type_of_expr m e dico
        | Hole d -> d.Type

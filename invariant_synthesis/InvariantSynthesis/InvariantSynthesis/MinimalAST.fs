module MinimalAST

    type Type = AST.Type
    type RepresentationInfos = AST.RepresentationInfos
    type ImplicationRule = AST.ImplicationRule

    type VarDecl = AST.VarDecl
    type FunDecl = AST.FunDecl
    type TypeDecl = AST.TypeDecl

    type ConstValue = AST.ConstValue

    type Value =
        | ValueConst of ConstValue
        | ValueVar of string
        | ValueFun of string * List<Value>
        | ValueEqual of Value * Value
        | ValueOr of Value * Value
        | ValueNot of Value
        | ValueSomeElse of VarDecl * Value * Value
        | ValueForall of VarDecl * Value
        | ValueInterpreted of string * List<Value>

    type HoleValue =
        | Hole of VarDecl
        | Expr of Value

    type Statement =
        | NewBlock of List<VarDecl> * List<Statement>
        | VarAssign of string * Value
        | VarAssignAction of string * string * List<Value>
        | FunAssign of string * List<HoleValue> * Value
        | IfElse of Value * Statement * Statement
        | IfSomeElse of VarDecl * Value * Statement * Statement
        | Assert of Value

    type ActionDecl = { Name: string; Args: List<VarDecl>; Output: VarDecl; Content: Statement }
    type MacroDecl = { Name: string; Args: List<VarDecl>; Output: Type; Value: Value ; Representation: RepresentationInfos }
    type InterpretedActionDecl<'a,'b> = AST.InterpretedActionDecl<'a,'b>
    [<NoEquality;NoComparison>]
    type ModuleDecl<'a,'b> =
        { Name: string; Types: List<TypeDecl>; Funs: List<FunDecl>; Vars: List<VarDecl>; InterpretedActions: List<InterpretedActionDecl<'a,'b>>;
            Actions: List<ActionDecl>; Invariants: List<Value>; Implications: List<ImplicationRule> }

    let value2minimal<'a,'b> (m:AST.ModuleDecl<'a,'b>) (v:AST.Value) =
        let rec aux v =
            match v with
            | AST.ValueConst cv -> ValueConst cv
            | AST.ValueVar str -> ValueVar str
            | AST.ValueFun (str, vs) -> ValueFun (str, List.map aux vs)
            | AST.ValueMacro (str, vs) ->
                let macro = AST.find_macro m str
                let v = AST.expand_macro macro vs
                aux v
            | AST.ValueEqual (v1, v2) -> ValueEqual (aux v1, aux v2)
            | AST.ValueOr (v1, v2) -> ValueOr (aux v1, aux v2)
            | AST.ValueAnd (v1, v2) ->
                aux (AST.ValueNot (AST.ValueOr (AST.ValueNot v1, AST.ValueNot v2)))
            | AST.ValueNot v -> ValueNot (aux v)
            | AST.ValueSomeElse (d,vsome,velse) -> ValueSomeElse (d,aux vsome,aux velse)
            | AST.ValueForall (d, v) -> ValueForall (d, aux v)
            | AST.ValueExists (d, v) ->
                aux (AST.ValueNot (AST.ValueForall (d, AST.ValueNot v)))
            | AST.ValueImply (v1, v2) ->
                aux (AST.ValueOr (AST.ValueNot v1, v2))
            | AST.ValueInterpreted (str, vs) -> ValueInterpreted (str, List.map aux vs)
        aux v

    // Operations on temporary var names

    let next_var = ref 0
    let reinit_tmp_vars () =
        next_var := 0

    let new_tmp_var () =
        let res = sprintf "%i" (!next_var)
        next_var := (!next_var) + 1
        AST.impossible_name res

    // Return a list of var action assignments + a minimal value
    let expr2minimal<'a,'b> (m:AST.ModuleDecl<'a,'b>) (e:AST.Expression) =
        let rec aux e =
            match e with
            | AST.ExprConst cv -> ([], ValueConst cv)
            | AST.ExprVar str -> ([], ValueVar str)
            | AST.ExprFun (str, es) ->
                let (vas,vs) = List.unzip (List.map aux es)
                (List.concat vas, ValueFun (str, vs))
            | AST.ExprMacro (str, vs) ->
                ([], value2minimal m (AST.ValueMacro (str,vs)))
            | AST.ExprAction (str, es) ->
                let (vas,vs) = List.unzip (List.map aux es)
                let tmp_name = new_tmp_var ()
                let va = (tmp_name, str, vs)
                let vas = (List.concat vas)@[va]
                (vas, ValueVar tmp_name)
            | AST.ExprEqual (e1, e2) ->
                let (vas1, v1) = aux e1
                let (vas2, v2) = aux e2
                (vas1@vas2, ValueEqual (v1, v2))
            | AST.ExprOr (e1, e2) ->
                let (vas1, v1) = aux e1
                let (vas2, v2) = aux e2
                (vas1@vas2, ValueOr (v1, v2))
            | AST.ExprAnd (e1, e2) ->
                let (vas1, v1) = aux e1
                let (vas2, v2) = aux e2
                (vas1@vas2, ValueNot (ValueOr (ValueNot v1, ValueNot v2)))
            | AST.ExprNot e ->
                let (vas, v) = aux e
                (vas, ValueNot v)
            | AST.ExprSomeElse (d, v1, v2) ->
                ([], ValueSomeElse (d, value2minimal m v1, value2minimal m v2))
            | AST.ExprForall (d, v) ->
                ([], ValueForall (d, value2minimal m v))
            | AST.ExprExists (d, v) ->
                ([], value2minimal m (AST.ValueExists (d,v)))
            | AST.ExprImply (e1, e2) ->
                let (vas1, v1) = aux e1
                let (vas2, v2) = aux e2
                (vas1@vas2, ValueOr (ValueNot v1, v2))
            | AST.ExprInterpreted (str, es) ->
                let (vas,vs) = List.unzip (List.map aux es)
                (List.concat vas, ValueInterpreted (str, vs))
        aux e

    let statement2minimal (s:AST.Statement) =
        match s with
        | AST.NewBlock (ds, sts) -> () // TODO

    let module2minimal<'a,'b> (m:AST.ModuleDecl<'a,'b>) =
        let actions = []
        let invariants = []

        { Name = m.Name; Types = m.Types; Funs = m.Funs; Vars = m.Vars; InterpretedActions = m.InterpretedActions;
            Actions = actions ; Invariants = invariants; Implications = m.Implications }

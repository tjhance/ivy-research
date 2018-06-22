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
        | Val of Value

    type Statement =
        | AtomicGroup of List<Statement>
        | NewBlock of List<VarDecl> * List<Statement>
        | VarAssign of string * Value
        | VarAssignAction of string * string * List<Value>
        | FunAssign of string * List<HoleValue> * Value
        | IfElse of Value * Statement * Statement
        | IfSomeElse of VarDecl * Value * Statement * Statement
        | Assert of Value
        | Assume of Value // TODO: Convert require/ensure to either assert or assume (depending on the context)
        // TODO: Handle the Assume case everywhere

    type ActionDecl = { Name: string; Args: List<VarDecl>; Output: VarDecl; Content: Statement }
    type MacroDecl = { Name: string; Args: List<VarDecl>; Output: Type; Value: Value ; Representation: RepresentationInfos }
    type InterpretedActionDecl<'a,'b> = AST.InterpretedActionDecl<'a,'b>
    [<NoEquality;NoComparison>]
    type ModuleDecl<'a,'b> =
        { Name: string; Types: List<TypeDecl>; Funs: List<FunDecl>; Vars: List<VarDecl>; InterpretedActions: List<InterpretedActionDecl<'a,'b>>;
            Actions: List<ActionDecl>; Invariants: List<Value>; Implications: List<ImplicationRule> }

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
                    let before = find_action m (AST.variant_action_name str "before") add_variants
                    { action with Content=NewBlock([],[before.Content;action.Content]) }
                with :? System.Collections.Generic.KeyNotFoundException -> action
            let action =
                try
                    let after = find_action m (AST.variant_action_name str "after") add_variants
                    { action with Content=NewBlock([],[action.Content;after.Content]) }
                with :? System.Collections.Generic.KeyNotFoundException -> action
            action
        else
            action

    let find_interpreted_action (m:ModuleDecl<'a,'b>) str =
        List.find (fun (decl:InterpretedActionDecl<'a,'b>) -> decl.Name = str) m.InterpretedActions

    // Conversion functions

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

    // Return a list of var decls & statements (var assignemnts) & a minimal value
    let expr2minimal<'a,'b> (m:AST.ModuleDecl<'a,'b>) (e:AST.Expression) =
        let new_var_assign v =
            let tmp_name = new_tmp_var ()
            let t = AST.Void // type_of_value m v _ // Note: For now, we don't need to bother with the type!
            let d = AST.default_var_decl tmp_name t
            let st = VarAssign (tmp_name, v)
            (d, st, tmp_name)
        let rec aux e =
            match e with
            | AST.ExprConst cv -> ([], [], ValueConst cv)
            | AST.ExprVar str ->
                let (d, st, name) = new_var_assign (ValueVar str)
                ([d], [st], ValueVar name)
            | AST.ExprFun (str, es) ->
                let (ds,sts,vs) = List.unzip3 (List.map aux es)
                let (d, st, name) = new_var_assign (ValueFun (str, vs))
                (d::(List.concat ds), (List.concat sts)@[st], ValueVar name)
            | AST.ExprMacro (str, vs) ->
                let (d, st, name) = new_var_assign (value2minimal m (AST.ValueMacro (str,vs)))
                ([d], [st], ValueVar name)
            | AST.ExprAction (str, es) ->
                let tmp_name = new_tmp_var ()
                let t = (AST.find_action m str false).Output.Type
                let d = AST.default_var_decl tmp_name t
                let (ds,sts,vs) = List.unzip3 (List.map aux es)
                let st = VarAssignAction (tmp_name, str, vs)
                (d::(List.concat ds), (List.concat sts)@[st], ValueVar tmp_name)
            | AST.ExprEqual (e1, e2) ->
                let (ds1, sts1, v1) = aux e1
                let (ds2, sts2, v2) = aux e2
                (ds1@ds2, sts1@sts2, ValueEqual (v1, v2))
            | AST.ExprOr (e1, e2) ->
                let (ds1, sts1, v1) = aux e1
                let (ds2, sts2, v2) = aux e2
                (ds1@ds2, sts1@sts2, ValueOr (v1, v2))
            | AST.ExprAnd (e1, e2) ->
                let (ds1, sts1, v1) = aux e1
                let (ds2, sts2, v2) = aux e2
                (ds1@ds2, sts1@sts2, ValueNot (ValueOr (ValueNot v1, ValueNot v2)))
            | AST.ExprNot e ->
                let (ds, sts, v) = aux e
                (ds, sts, ValueNot v)
            | AST.ExprSomeElse (d, v1, v2) ->
                ([], [], ValueSomeElse (d, value2minimal m v1, value2minimal m v2))
            | AST.ExprForall (d, v) ->
                ([], [], ValueForall (d, value2minimal m v))
            | AST.ExprExists (d, v) ->
                ([], [], value2minimal m (AST.ValueExists (d,v)))
            | AST.ExprImply (e1, e2) ->
                let (ds1, sts1, v1) = aux e1
                let (ds2, sts2, v2) = aux e2
                (ds1@ds2, sts1@sts2, ValueOr (ValueNot v1, v2))
            | AST.ExprInterpreted (str, es) ->
                let (ds,sts,vs) = List.unzip3 (List.map aux es)
                let (d, st, name) = new_var_assign (ValueInterpreted (str, vs))
                (d::(List.concat ds), (List.concat sts)@[st], ValueVar name)
        aux e

    let exprs2minimal<'a,'b> (m:AST.ModuleDecl<'a,'b>) es =
        let (ds, sts, vs) = List.unzip3 (List.map (expr2minimal m) es)
        (List.concat ds, List.concat sts, vs)

    let rec exprs_of_hexprs hexprs =
        match hexprs with
        | [] -> []
        | (AST.Hole _)::lst -> exprs_of_hexprs lst
        | (AST.Expr e)::lst -> e::(exprs_of_hexprs lst)

    let rec hvals_of_hexprs hexprs vals =
        match hexprs, vals with
        | [], [] -> []
        | (AST.Hole h)::lst, vals -> (Hole h)::(hvals_of_hexprs lst vals)
        | (AST.Expr _)::lst, v::vals -> (Val v)::(hvals_of_hexprs lst vals)
        | _ -> failwith "Invalid HoleExpression!"

    let statement2minimal<'a,'b> (m:AST.ModuleDecl<'a,'b>) (s:AST.Statement) =
        reinit_tmp_vars ()
        let packIfNecessary decls sts =
            if List.length sts = 1 && List.isEmpty decls
            then List.head sts
            else NewBlock (decls, sts)
        let group_sts sts =
            [AtomicGroup (sts)]
        // Returns a list of var decls + a list of statements
        let rec aux s =
            match s with
            | AST.NewBlock (ds, sts) ->
                let (nds, sts) = List.unzip (List.map aux sts)
                ([], [NewBlock (List.concat (ds::nds), List.concat sts)])
            | AST.Expression e ->
                let (ds, sts, _) = expr2minimal m e
                (ds, group_sts sts)
            | AST.VarAssign (str, e) ->
                let (ds, sts, v) = expr2minimal m e
                let st = VarAssign (str, v)
                (ds, group_sts (sts@[st]))
            | AST.FunAssign (str, es, e) ->
                let (ds1, sts1, vs) = exprs2minimal m es
                let (ds2, sts2, v) = expr2minimal m e
                let (ds, sts) = (ds1@ds2, sts1@sts2)
                let st = FunAssign (str, List.map (fun v -> Val v) vs, v)
                (ds, group_sts (sts@[st]))
            | AST.ForallFunAssign (str, hes, v) ->
                let es = exprs_of_hexprs hes
                let (ds, sts, vs) = exprs2minimal m es
                let v = value2minimal m v
                let st = FunAssign (str, hvals_of_hexprs hes vs, v)
                (ds, group_sts (sts@[st]))
            | AST.IfElse (e, sif, selse) ->
                let (ds, sts, v) = expr2minimal m e
                let (dsif, sif) = aux sif
                let (dselse, selse) = aux selse
                let st = IfElse (v, packIfNecessary dsif sif, packIfNecessary dselse selse)
                (ds, group_sts (sts@[st]))
            | AST.IfSomeElse (d, v, sif, selse) ->
                let v = value2minimal m v
                let (dsif, sif) = aux sif
                let (dselse, selse) = aux selse
                let st = IfSomeElse (d, v, packIfNecessary dsif sif, packIfNecessary dselse selse)
                ([], [st])
            | AST.Assert v -> ([], [Assert (value2minimal m v)])
        let (decls, sts) = aux s
        packIfNecessary decls sts

    let module2minimal<'a,'b> (m:AST.ModuleDecl<'a,'b>) =
        let action2minimal (a:AST.ActionDecl) =
            let st = statement2minimal m a.Content
            { ActionDecl.Name = a.Name; ActionDecl.Args = a.Args ; ActionDecl.Output = a.Output ; ActionDecl.Content = st }

        let actions = List.map action2minimal m.Actions
        let invariants = List.map (value2minimal m) m.Invariants

        { Name = m.Name; Types = m.Types; Funs = m.Funs; Vars = m.Vars; InterpretedActions = m.InterpretedActions;
            Actions = actions ; Invariants = invariants; Implications = m.Implications }

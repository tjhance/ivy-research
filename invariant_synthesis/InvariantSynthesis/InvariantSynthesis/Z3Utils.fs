module Z3Utils

    open MinimalAST
    open WPR
    open Microsoft.Z3

    let sort_of_type (ctx:Context) sorts t : Sort =
        match t with
        | AST.Void -> failwith "Void type has no sort!"
        | AST.Bool -> ctx.BoolSort :> Sort
        | AST.Uninterpreted str -> Map.find str sorts :> Sort

    [<NoComparison>]
    type ModuleContext =
        {
            Context: Context ; Sorts: Map<string, UninterpretedSort> ;
            Vars: Map<string, FuncDecl> ; Funs: Map<string, FuncDecl>
        }

    let build_context<'a,'b> (m:ModuleDecl<'a,'b>) =
        let ctx = new Context()
        let sorts = ref Map.empty 
        let vars = ref Map.empty
        let funs = ref Map.empty

        for d in m.Types do
            sorts := Map.add d.Name (ctx.MkUninterpretedSort(d.Name)) (!sorts)
        for d in m.Funs do
            let domain = List.map (sort_of_type ctx (!sorts)) d.Input
            let range = sort_of_type ctx (!sorts) d.Output
            funs := Map.add d.Name (ctx.MkFuncDecl(d.Name,Array.ofList domain,range)) (!funs)
        for d in m.Vars do
            let range = sort_of_type ctx (!sorts) d.Type
            vars := Map.add d.Name (ctx.MkConstDecl(d.Name, range)) (!vars)

        { Context = ctx ; Sorts = !sorts ; Vars = !vars ; Funs = !funs }

    let name_of_constint (t,i) =
        sprintf "%s%c%i" t AST.name_separator i

    let declare_lvars<'a,'b> (m:ModuleDecl<'a,'b>) action (ctx:ModuleContext) v =
        
        let action = find_action m action false

        let add_civ acc (t,i) =
            let name = name_of_constint (t,i)
            let sort = Map.find t ctx.Sorts
            if not (Map.containsKey name acc)
            then Map.add name (ctx.Context.MkConstDecl(name,sort)) acc
            else acc

        let add_fv acc name =
            let decl = List.find (fun (v:VarDecl) -> v.Name = name) action.Args
            match decl.Type with
            | AST.Void | AST.Bool -> acc
            | AST.Uninterpreted t ->
                let sort = Map.find t ctx.Sorts
                if not (Map.containsKey name acc)
                then Map.add name (ctx.Context.MkConstDecl(name,sort)) acc
                else acc
        
        let lvars = Set.fold add_civ Map.empty (const_int_in_value v)
        Set.fold add_fv lvars (free_vars_of_value v)

    let expr_of_cv (ctx:Context) lvars cv =
        match cv with
        | AST.ConstVoid -> failwith "Void value is not a valid expression!"
        | AST.ConstBool true -> ctx.MkTrue() :> Expr
        | AST.ConstBool false -> ctx.MkFalse() :> Expr
        | AST.ConstInt (t, i) ->
            let name = name_of_constint (t,i)
            let fd = Map.find name lvars
            ctx.MkConst(fd)

    let build_value<'a,'b> (m:ModuleDecl<'a,'b>) (ctx:ModuleContext) main_action (v:Z3Value) =

        let lvars = declare_lvars m main_action ctx v

        let rec aux qvars v =
            match v with
            | Z3Const cv -> expr_of_cv ctx.Context lvars cv
            | Z3Var str ->
                if Map.containsKey str lvars
                then ctx.Context.MkConst (Map.find str lvars)
                else Map.find str qvars
            | Z3Fun (str, vs) ->
                let exprs = List.map (aux qvars) vs
                let fd = Map.find str ctx.Funs
                ctx.Context.MkApp (fd, exprs)
            | Z3Equal (v1, v2) ->
                let e1 = aux qvars v1
                let e2 = aux qvars v2
                ctx.Context.MkEq (e1, e2) :> Expr
            | Z3Or (v1, v2) ->
                let e1 = aux qvars v1 :?> BoolExpr
                let e2 = aux qvars v2 :?> BoolExpr
                ctx.Context.MkOr ([e1;e2]) :> Expr
            | Z3And (v1, v2) ->
                let e1 = aux qvars v1 :?> BoolExpr
                let e2 = aux qvars v2 :?> BoolExpr
                ctx.Context.MkAnd ([e1;e2]) :> Expr
            | Z3Imply (v1, v2) ->
                let e1 = aux qvars v1 :?> BoolExpr
                let e2 = aux qvars v2 :?> BoolExpr
                ctx.Context.MkImplies (e1,e2) :> Expr
            | Z3Not v ->
                let e = aux qvars v :?> BoolExpr
                ctx.Context.MkNot (e) :> Expr
            | Z3IfElse (vc, vif, velse) ->
                let ec = aux qvars vc :?> BoolExpr
                let eif = aux qvars vif
                let eelse = aux qvars velse
                ctx.Context.MkITE (ec, eif, eelse)
            | Z3Forall (d, v) ->
                let cst = ctx.Context.MkConst (d.Name, sort_of_type ctx.Context ctx.Sorts d.Type)
                let qvars = Map.add d.Name cst qvars
                let e = aux qvars v
                ctx.Context.MkForall ([|cst|], e) :> Expr
            | Z3Exists (d, v) ->
                let cst = ctx.Context.MkConst (d.Name, sort_of_type ctx.Context ctx.Sorts d.Type)
                let qvars = Map.add d.Name cst qvars
                let e = aux qvars v
                ctx.Context.MkExists ([|cst|], e) :> Expr
            | Z3Declare (d, v, b) ->
                let b = replace_var d.Name v b
                aux qvars b
            | Z3Hole -> failwith "Can't convert a context to a Z3 formula!"
        aux Map.empty v

    let check (ctx:ModuleContext) (e:Expr) =
        let s = ctx.Context.MkSolver()
        s.Assert ([|e:?> BoolExpr|])
        match s.Check () with
        | Status.UNKNOWN ->
            printfn "ERROR: Satisfiability can't be decided! Assuming unSAT."
            None
        | Status.UNSATISFIABLE ->
            None
        | Status.SATISFIABLE ->
            Some s.Model
        | _ -> failwith "Solver returned an unknown status..."

    //let z3model_to_ast_model model:Model =
        
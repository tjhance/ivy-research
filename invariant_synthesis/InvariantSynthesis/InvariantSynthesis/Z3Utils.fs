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
        
        let args = (find_action m action).Args

        let add_civ (lvars,z3concrete_map) (t,i) =
            let name = name_of_constint (t,i)
            let sort = Map.find t ctx.Sorts
            if not (Map.containsKey name lvars)
            then
                let lvars = Map.add name (ctx.Context.MkConstDecl(name,sort)) lvars
                let z3concrete_map = (name, (t,i))::z3concrete_map
                (lvars,z3concrete_map)
            else (lvars,z3concrete_map)

        let add_fv acc name =
            if Map.containsKey name ctx.Vars
            then acc
            else if Map.containsKey name acc
            then acc
            else
                let decl = List.find (fun (v:VarDecl) -> v.Name = name) args
                let sort = sort_of_type ctx.Context ctx.Sorts decl.Type
                Map.add name (ctx.Context.MkConstDecl(name,sort)) acc
        
        let (lvars,z3concrete_map) = Set.fold add_civ (Map.empty,[]) (const_int_in_value v)
        let lvars = Set.fold add_fv lvars (free_vars_of_value v)
        (lvars,z3concrete_map)

    let expr_of_cv (ctx:Context) lvars cv =
        match cv with
        | AST.ConstVoid -> failwith "Void value is not a valid expression!"
        | AST.ConstBool true -> ctx.MkTrue() :> Expr
        | AST.ConstBool false -> ctx.MkFalse() :> Expr
        | AST.ConstInt (t, i) ->
            let name = name_of_constint (t,i)
            let fd = Map.find name lvars
            ctx.MkConst(fd)

    let build_value<'a,'b> (ctx:ModuleContext) lvars (v:Z3Value) =

        let rec aux qvars v =
            match v with
            | Z3Const cv -> expr_of_cv ctx.Context lvars cv
            | Z3Var str ->
                if Map.containsKey str ctx.Vars
                then ctx.Context.MkConst (Map.find str ctx.Vars)
                else if Map.containsKey str lvars
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

    let cv_of_expr_str const_cv_map str =
        match str with
        | "true" -> AST.ConstBool true
        | "false" -> AST.ConstBool false
        | str -> AST.ConstInt (Map.find str const_cv_map)

    let rec universe_for_sorts (ctx:ModuleContext) (model:Model) (sorts:List<Sort>) =
        match sorts with
        | [] -> Seq.singleton []
        | s::sorts ->
            let res = universe_for_sorts ctx model sorts
            let univ = model.SortUniverse (s)
            let res = Seq.map (fun lst -> Seq.map (fun e -> e::lst) univ) res
            Seq.concat res

    let z3model_to_ast_model<'a,'b> (m:AST.ModuleDecl<'a,'b>) (ctx:ModuleContext) args lvars 
        z3concrete_map (model:Model)
        : (Model.TypeInfos * Model.Environment * Map<string, AST.ConstValue>) =

        let all_decls = model.Decls
        let is_declared (fd:FuncDecl) =
            Array.exists (fun (fd':FuncDecl) -> fd.Name = fd'.Name) all_decls

        // Fix concrete const values
        let treat_concrete const_cv_map (name,cv) =
            let (fd:FuncDecl) = Map.find name lvars
            if is_declared fd
            then
                let (e:Expr) = model.ConstInterp (fd)
                let fname = e.FuncDecl.Name.ToString()
                Map.add fname cv const_cv_map
            else const_cv_map
        let const_cv_map = List.fold treat_concrete Map.empty z3concrete_map

        let treat_type const_cv_map (t:AST.TypeDecl) =
            let sort = Map.find t.Name ctx.Sorts
            let univ = model.SortUniverse (sort)
            let treat_expr const_cv_map (e:Expr) =
                let rec next_available_i i =
                    match Map.tryFindKey (fun _ (str,j) -> str=t.Name && j=i) const_cv_map with
                    | None -> i
                    | Some _ -> next_available_i (i+1)
                let name = e.FuncDecl.Name.ToString()
                let const_cv_map = Map.add name (t.Name, next_available_i 0) const_cv_map
                const_cv_map
            Array.fold treat_expr const_cv_map univ
        let const_cv_map = List.fold treat_type const_cv_map m.Types

        // Type infos
        let type_infos = List.fold (fun acc (t:AST.TypeDecl) -> Map.add t.Name 0 acc) Map.empty m.Types
        let update_type_infos acc (_,(t,i)) =
            let new_i = max i (Map.find t acc)
            Map.add t new_i acc
        let type_infos = List.fold update_type_infos type_infos (Map.toList const_cv_map)

        // Environment
        let cv_of_expr (e:Expr) =
            cv_of_expr_str const_cv_map (e.FuncDecl.Name.ToString())

        let treat_var (fd_map:Map<string,FuncDecl>) acc (decl:VarDecl) =
            let fd = Map.find decl.Name fd_map
            if is_declared fd
            then
                let expr = model.ConstInterp (fd)
                let cv = cv_of_expr expr
                Map.add decl.Name cv acc
            else
                Map.add decl.Name (AST.type_default_value decl.Type) acc

        let var_env = List.fold (treat_var ctx.Vars) Map.empty m.Vars
        let lvars_env = List.fold (treat_var lvars) Map.empty args

        let treat_fun acc (d:AST.FunDecl) =
            // Default vals
            let all_entries = Model.all_values_ext type_infos d.Input
            let default_val = AST.type_default_value d.Output
            let acc = Seq.fold (fun acc cvs -> Map.add (d.Name, cvs) default_val acc) acc all_entries
            // Z3 Entries
            let fd = Map.find d.Name ctx.Funs
            if is_declared fd
            then
                let fi = model.FuncInterp (fd)
                // Else case
                let expr = fi.Else
                let treat_else_case_for acc exprs =
                    let exprs = Array.ofList exprs
                    (*let exprs = Array.sub exprs 0 (Array.length expr.Args)
                    let expr = model.Eval(expr.Substitute(expr.Args, exprs),false)*)
                    // Note: Right way to do???
                    let expr = model.Eval(expr.SubstituteVars(exprs),false)
                    let cv = cv_of_expr expr
                    let cvs = List.ofArray (Array.map cv_of_expr exprs)
                    Map.add (d.Name, cvs) cv acc
                let acc = Seq.fold treat_else_case_for acc (universe_for_sorts ctx model (List.ofArray fd.Domain))
                // Entries
                let entries = fi.Entries
                let aux acc (entry:FuncInterp.Entry) =
                    let input_expr = entry.Args
                    let input = Array.toList (Array.map cv_of_expr input_expr)
                    let expr = entry.Value
                    let cv = cv_of_expr expr
                    Map.add (d.Name, input) cv acc
                Array.fold aux acc entries
            else acc

        let fun_env = List.fold treat_fun Map.empty m.Funs

        (type_infos, { Model.Environment.f = fun_env ; Model.Environment.v = var_env }, lvars_env)

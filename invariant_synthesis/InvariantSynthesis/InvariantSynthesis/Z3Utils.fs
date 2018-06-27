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

        let rec aux v =
            match v with
            | Z3Const cv -> expr_of_cv ctx.Context lvars cv

        aux v

    (*
        type Z3Value =
        | Z3Const of ConstValue
        | Z3Var of string
        | Z3Fun of string * List<Z3Value>
        | Z3Equal of Z3Value * Z3Value
        | Z3Or of Z3Value * Z3Value
        | Z3And of Z3Value * Z3Value
        | Z3Imply of Z3Value * Z3Value
        | Z3Not of Z3Value
        | Z3IfElse of Z3Value * Z3Value * Z3Value
        | Z3Forall of VarDecl * Z3Value
        | Z3Exists of VarDecl * Z3Value
        | Z3Declare of VarDecl * Z3Value * Z3Value
        | Z3Hole // Used for contexts
    *)
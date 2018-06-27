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

    let buildContext<'a,'b> (m:ModuleDecl<'a,'b>) =
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
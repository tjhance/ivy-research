module WPR

    open MinimalAST

    type Statement =
        | NewBlock of List<VarDecl> * List<Statement>
        | VarAssign of string * Value
        | VarAssignAction of string * string * List<Value>
        | FunAssign of string * List<VarDecl> * Value
        | Parallel of Statement * Statement
        | Assume of Value
        | Abort

    let minimal_stat2wpr_stat st =
        let packIfNecessary sts =
            if List.length sts = 1 then List.head sts
            else NewBlock ([],sts)
        let rec aux st =
            match st with
            | MinimalAST.AtomicGroup sts -> List.concat (List.map aux sts)
            | MinimalAST.NewBlock (decls, sts) ->
                [NewBlock (decls, List.concat (List.map aux sts))]
            | MinimalAST.VarAssign (str, v) ->
                [VarAssign (str, v)]
            | MinimalAST.VarAssignAction (str, action, vs) ->
                [VarAssignAction (str, action, vs)]
           // | MinimalAST.FunAssign (str, hvs, v) ->
           // TODO
        packIfNecessary (aux st)
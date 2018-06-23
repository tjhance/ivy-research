module WPR

    // Thanks to https://github.com/Microsoft/ivy/blob/master/doc/decidability.md

    open MinimalAST

    type Statement =
        | NewBlock of List<VarDecl> * List<Statement>
        | VarAssign of string * Value
        | VarAssignAction of string * string * List<Value>
        | FunAssign of string * List<VarDecl> * Value
        | Parallel of Statement * Statement
        | Assume of Value
        | Abort

    let next_qvar = ref 0

    let reinit_tmp_qvars () =
        next_qvar := 0

    let new_tmp_qvar () =
        let res = sprintf "%i" (!next_qvar)
        next_qvar := (!next_qvar) + 1
        AST.impossible_qname res

    let minimal_stat2wpr_stat<'a,'b> (m:ModuleDecl<'a,'b>) st =
        reinit_tmp_qvars ()

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
            | MinimalAST.FunAssign (str, hvs, v) ->
                let (vs, ds) = Interpreter.separate_hvals hvs
                let added_names = List.init (List.length vs) (fun _ -> new_tmp_qvar ())
                
                let names = List.map (fun (d:VarDecl) -> d.Name) ds
                let names = Interpreter.reconstruct_hvals hvs added_names names
                let decls = List.map2 (fun n (d:VarDecl) -> AST.default_var_decl n d.Type) names (find_action m str false).Args
                
                let add_condition acc name vcond =
                    let vcond = ValueEqual (vcond, ValueVar name)
                    ValueIfElse (vcond, acc, ValueFun (str, List.map (fun str -> ValueVar str) names))
                let v = List.fold2 add_condition v added_names vs
                [FunAssign (str,decls,v)]
            | MinimalAST.IfElse (vcond, sif, selse) ->
                let sif = (Assume vcond)::(aux sif)
                let sif = packIfNecessary sif
                let selse = (Assume (ValueNot vcond))::(aux selse)
                let selse = packIfNecessary selse
                [Parallel (sif, selse)]
            | MinimalAST.IfSomeElse (d, vcond, sif, selse) ->
                let qvar_name = new_tmp_qvar ()
                let qvar = AST.default_var_decl qvar_name d.Type
                let vcond_qvar = map_vars_in_value vcond (Map.add d.Name (ValueVar qvar_name) Map.empty)
                let sif = aux sif
                let sif_d_assign = ValueSomeElse (qvar, vcond_qvar, ValueConst (AST.type_default_value d.Type))
                let sif = [NewBlock ([d], (VarAssign (d.Name, sif_d_assign))::sif)]
                let sif = (Assume (ValueNot (ValueForall (qvar, ValueNot vcond_qvar))))::sif
                let sif = packIfNecessary sif
                let selse = (Assume (ValueForall (qvar, ValueNot vcond_qvar)))::(aux selse)
                let selse = packIfNecessary selse
                [Parallel (sif, selse)]
            | MinimalAST.Assert v ->
                let sassert = [Assume (ValueNot v);Abort]
                let sassert = packIfNecessary sassert
                [Parallel (sassert,NewBlock([],[]))]
            | MinimalAST.Assume v ->
                [Assume v]
        packIfNecessary (aux st)
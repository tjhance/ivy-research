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

    let next_var = ref 0

    let reinit_tmp_vars () =
        next_var := 0

    let unique_name name =
        let id = !next_var
        next_var := (!next_var) + 1
        AST.make_name_unique name id

    // We convert the AST to a simpler one & we rename each local variable in order for them to be unique
    let minimal_stat2wpr_stat<'a,'b> (m:ModuleDecl<'a,'b>) renaming st =
        let packIfNecessary sts =
            if List.length sts = 1 then List.head sts
            else NewBlock ([],sts)
        let rename_value renaming v =
            let dico = Map.map (fun _ str -> ValueVar str) renaming
            map_vars_in_value v dico
        let rename_var renaming str =
            if Map.containsKey str renaming
            then Map.find str renaming else str

        let rec aux renaming st =
            match st with
            | MinimalAST.AtomicGroup sts -> List.concat (List.map (aux renaming) sts)
            | MinimalAST.NewBlock (decls, sts) ->
                let new_decls = List.map (fun (d:VarDecl) -> AST.default_var_decl (unique_name d.Name) d.Type) decls
                let renaming = List.fold2 (fun acc (od:VarDecl) (nd:VarDecl) -> Map.add od.Name nd.Name acc) renaming decls new_decls
                [NewBlock (new_decls, List.concat (List.map (aux renaming) sts))]
            | MinimalAST.VarAssign (str, v) ->
                [VarAssign (rename_var renaming str, rename_value renaming v)]
            | MinimalAST.VarAssignAction (str, action, vs) ->
                [VarAssignAction (rename_var renaming str, action, List.map (rename_value renaming) vs)]
            | MinimalAST.FunAssign (str, hvs, v) ->
                let (vs, ds) = Interpreter.separate_hvals hvs
                let vs = List.map (rename_value renaming) vs
                let added_names = List.init (List.length vs) (fun _ -> unique_name (AST.local_name "FAV"))
                
                let new_ds = List.map (fun (d:VarDecl) -> AST.default_var_decl (unique_name d.Name) d.Type) ds
                let renaming = List.fold2 (fun acc (od:VarDecl) (nd:VarDecl) -> Map.add od.Name nd.Name acc) renaming ds new_ds
                let names = List.map (fun (d:VarDecl) -> d.Name) new_ds
                let names = Interpreter.reconstruct_hvals hvs added_names names
                let decls = List.map2 (fun n (d:VarDecl) -> AST.default_var_decl n d.Type) names (find_action m str false).Args
                
                let v = rename_value renaming v
                let add_condition acc name vcond =
                    let vcond = ValueEqual (vcond, ValueVar name)
                    ValueIfElse (vcond, acc, ValueFun (str, List.map (fun str -> ValueVar str) names))
                let v = List.fold2 add_condition v added_names vs

                [FunAssign (str,decls,v)]
            | MinimalAST.IfElse (vcond, sif, selse) ->
                let vcond = rename_value renaming vcond
                let sif = (Assume vcond)::(aux renaming sif)
                let sif = packIfNecessary sif
                let selse = (Assume (ValueNot vcond))::(aux renaming selse)
                let selse = packIfNecessary selse
                [Parallel (sif, selse)]
            | MinimalAST.IfSomeElse (d, vcond, sif, selse) ->
                let qvar = AST.default_var_decl (unique_name (AST.local_name "ISE")) d.Type
                let renaming_qvar = Map.add d.Name qvar.Name renaming
                let vcond_qvar = rename_value renaming_qvar vcond

                let selse = aux renaming selse
                let selse = (Assume (ValueForall (qvar, ValueNot vcond_qvar)))::selse
                let selse = packIfNecessary selse

                let new_d = AST.default_var_decl (unique_name d.Name) d.Type
                let renaming_d = Map.add d.Name new_d.Name renaming
                
                let sif = aux renaming_d sif
                let sif_d_assign = ValueSomeElse (qvar, vcond_qvar, ValueConst (AST.type_default_value d.Type))
                let sif = [NewBlock ([new_d], (VarAssign (new_d.Name, sif_d_assign))::sif)]
                let sif = (Assume (ValueNot (ValueForall (qvar, ValueNot vcond_qvar))))::sif
                let sif = packIfNecessary sif
                
                [Parallel (sif, selse)]
            | MinimalAST.Assert v ->
                let v = rename_value renaming v
                let sassert = [Assume (ValueNot v);Abort]
                let sassert = packIfNecessary sassert
                [Parallel (sassert,NewBlock([],[]))]
            | MinimalAST.Assume v ->
                let v = rename_value renaming v
                [Assume v]
        packIfNecessary (aux renaming st)

    type ActionDecl = { Name: string; Args: List<VarDecl>; Output: VarDecl; Content: Statement }

    let minimal_actions2wpr_action<'a,'b> (m:ModuleDecl<'a,'b>) (action:MinimalAST.ActionDecl) rename_args =
        let rename_decl renaming (decl:VarDecl) =
            if Map.containsKey decl.Name renaming
            then { decl with Name = Map.find decl.Name renaming } else decl

        let renaming =
            if rename_args
            then List.fold (fun acc (d:VarDecl) -> Map.add d.Name (unique_name d.Name) acc) Map.empty (action.Output::action.Args)
            else Map.empty
        let args = List.map (rename_decl renaming) action.Args
        let output = rename_decl renaming action.Output
        { Name = action.Name ; Args = args ; Output = output ; Content = minimal_stat2wpr_stat m renaming action.Content }
        
    (*let weakest_precondition<'a,'b> (m:ModuleDecl<'a,'b>) f st =
        let rec aux f st =
            match st with
            | NewBlock (ds, sts) ->
                List.fold aux f (List.rev sts)

        aux f (minimal_stat2wpr_stat m st)*)
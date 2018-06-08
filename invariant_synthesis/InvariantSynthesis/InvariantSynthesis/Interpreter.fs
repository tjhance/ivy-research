module Interpreter

    open AST

    // Note: In synthesis.fs, operations like Set.contains or Set.remove doesn't take value_equal into account.
    let value_equal _ v1 v2 = v1=v2

    let value_or v1 v2 =
        match v1, v2 with
        | ConstBool b1, ConstBool b2 -> ConstBool (b1 || b2)
        | _ -> ConstVoid

    let value_and v1 v2 =
        match v1, v2 with
        | ConstBool b1, ConstBool b2 -> ConstBool (b1 && b2)
        | _ -> ConstVoid

    let value_not v =
        match v with
        | ConstBool b -> ConstBool (not b)
        | _ -> ConstVoid

    let value_imply v1 v2 =
        match v1, v2 with
        | ConstBool b1, ConstBool b2 -> ConstBool ((not b1) || b2)
        | _ -> ConstVoid

    let rec if_some_value (m:ModuleDecl) infos (env:Model.Environment) (decl:VarDecl) v : option<ConstValue> =
        let possible_values = Model.all_values infos (decl.Type)
        try
            Some (Seq.find (fun cv -> eval_value_with m infos env v [decl.Name] [cv] = ConstBool true) possible_values)
        with :? System.Collections.Generic.KeyNotFoundException -> None

    and evaluate_value (m:ModuleDecl) infos (env:Model.Environment) v =
        match v with
        | ValueConst cv -> cv
        | ValueVar str -> Map.find str env.v
        | ValueFun (str, lst) ->
            let lst = List.map (evaluate_value m infos env) lst
            Map.find (str, lst) env.f
        | ValueMacro (str, lst) -> // For now, we don't check the types
            let macro = find_macro m str
            let dico = List.fold2 (fun acc (d:VarDecl) v -> Map.add d.Name v acc) Map.empty macro.Args lst
            let v = map_vars_in_value (macro.Value) dico
            evaluate_value m infos env v
        | ValueEqual (v1, v2) ->
            let cv1 = evaluate_value m infos env v1
            let cv2 = evaluate_value m infos env v2
            ConstBool (value_equal env cv1 cv2)
        | ValueOr (v1, v2) -> 
            let cv1 = evaluate_value m infos env v1
            let cv2 = evaluate_value m infos env v2
            value_or cv1 cv2
        | ValueAnd (v1, v2) -> 
            let cv1 = evaluate_value m infos env v1
            let cv2 = evaluate_value m infos env v2
            value_and cv1 cv2
        | ValueNot v -> 
            let cv = evaluate_value m infos env v
            value_not cv
        | ValueSomeElse (d,f,v) ->
            match if_some_value m infos env d f with
            | Some v -> v
            | None -> evaluate_value m infos env v
        | ValueForall (d,v) ->
            let possible_values = Model.all_values infos d.Type
            ConstBool (Seq.forall (fun cv -> eval_value_with m infos env v [d.Name] [cv] = ConstBool true) possible_values)
        | ValueExists (d,v) ->
            let possible_values = Model.all_values infos d.Type
            ConstBool (Seq.exists (fun cv -> eval_value_with m infos env v [d.Name] [cv] = ConstBool true) possible_values)
        | ValueImply (v1,v2) ->
            evaluate_value m infos env (ValueOr (ValueNot v1, v2))

    and eval_value_with (m:ModuleDecl) infos (env:Model.Environment) v names values =
        let v' = List.fold2 (fun acc n v -> Map.add n v acc) env.v names values
        evaluate_value m infos { env with v=v' } v

    exception AssertionFailed of Model.Environment * Value

    let enter_new_block infos (env:Model.Environment) lvars lvalues : Model.Environment =
        let add_decl acc (decl:VarDecl) v =
            match v with
            | None -> Map.add decl.Name (Model.pick_value infos decl.Type) acc
            | Some v -> Map.add decl.Name v acc
        {env with v=List.fold2 add_decl env.v lvars lvalues }

    let leave_block _ (env:Model.Environment) lvars (old_env:Model.Environment) : Model.Environment =
        let rollback acc (decl:VarDecl) =
            match Map.tryFind decl.Name old_env.v with
            | None -> Map.remove decl.Name acc
            | Some e -> Map.add decl.Name e acc
        { env with v=List.fold rollback env.v lvars }

    let rec reconstruct_hexpression hes vs uvs =
        match hes with
        | [] -> []
        | (Hole _)::hes -> (List.head uvs)::(reconstruct_hexpression hes vs (List.tail uvs))
        | (Expr _)::hes -> (List.head vs)::(reconstruct_hexpression hes (List.tail vs) uvs)

    let rec reconstruct_hexpression_opt hes vs =
        match hes with
        | [] -> []
        | (Hole _)::hes -> None::(reconstruct_hexpression_opt hes vs)
        | (Expr _)::hes -> (Some (List.head vs))::(reconstruct_hexpression_opt hes (List.tail vs))

    let rec reconstruct_hexpression_opt2 hes vs =
        match hes with
        | [] -> []
        | (Hole _)::hes -> None::(reconstruct_hexpression_opt2 hes vs)
        | (Expr _)::hes -> (List.head vs)::(reconstruct_hexpression_opt2 hes (List.tail vs))

    let separate_hexpression hes =
        // Fixed expressions
        let exprs = List.filter (fun he -> match he with Hole _ -> false | Expr _ -> true) hes
        let exprs = List.map (fun he -> match he with Hole _ -> failwith "" | Expr e -> e) exprs
        // Universally quantified vars
        let uvars = List.filter (fun he -> match he with Hole _ -> true | Expr _ -> false) hes
        let uvars = List.map (fun he -> match he with Hole d -> d | Expr _ -> failwith "") uvars
        (exprs, uvars)

    let rec keep_only_expr_hexpression hes res =
        match hes with
        | [] -> []
        | (Hole _)::hes -> keep_only_expr_hexpression hes (List.tail res)
        | (Expr _)::hes -> (List.head res)::(keep_only_expr_hexpression hes (List.tail res))

    let rec keep_only_hole_hexpression hes res =
        match hes with
        | [] -> []
        | (Hole _)::hes -> (List.head res)::(keep_only_hole_hexpression hes (List.tail res))
        | (Expr _)::hes -> keep_only_hole_hexpression hes (List.tail res)

    let rec evaluate_expression (m:ModuleDecl) infos (env:Model.Environment) e =
        match e with
        | ExprConst cv -> (env, cv)
        | ExprVar v -> (env, evaluate_value m infos env (ValueVar v))
        | ExprFun (str, lst) ->
            let (env, lst) = evaluate_expressions m infos env lst
            let lst = List.map (fun cv -> ValueConst cv) lst
            (env, evaluate_value m infos env (ValueFun (str, lst)))
        | ExprMacro (str, lst) ->
            (env, evaluate_value m infos env (ValueMacro (str, lst)))
        | ExprAction (str, lst) ->
            let (env, lst) = evaluate_expressions m infos env lst
            execute_action m infos env str lst
        | ExprEqual (e1, e2) ->
            let (env, v1) = evaluate_expression m infos env e1
            let (env, v2) = evaluate_expression m infos env e2
            (env, ConstBool (value_equal env v1 v2))
        | ExprOr (e1, e2) -> 
            let (env, v1) = evaluate_expression m infos env e1
            let (env, v2) = evaluate_expression m infos env e2
            (env, value_or v1 v2)
        | ExprAnd (e1, e2) -> 
            let (env, v1) = evaluate_expression m infos env e1
            let (env, v2) = evaluate_expression m infos env e2
            (env, value_and v1 v2)
        | ExprNot e -> 
            let (env, v) = evaluate_expression m infos env e
            (env, value_not v)
        | ExprSomeElse (d,v,e) ->
            (env, evaluate_value m infos env (ValueSomeElse (d,v,e)))
        | ExprForall (d,v) ->
            (env, evaluate_value m infos env (ValueForall (d,v)))
        | ExprExists (d,v) ->
            (env, evaluate_value m infos env (ValueExists (d,v)))
        | ExprImply (e1, e2) -> 
            let (env, v1) = evaluate_expression m infos env e1
            let (env, v2) = evaluate_expression m infos env e2
            (env, value_imply v1 v2)

    and evaluate_expressions (m:ModuleDecl) infos (env:Model.Environment) es =
        let aux (env, res) e =
            let (env, v) = evaluate_expression m infos env e
            (env, v::res)
        let (env, res) = List.fold aux (env, []) es
        (env, List.rev res)

    and execute_statement (m:ModuleDecl) infos (env:Model.Environment) s : Model.Environment =
        match s with
        | NewBlock (decls, ss) ->
            let env' = enter_new_block infos env decls (List.map (fun _ -> None) decls)
            let env' = execute_statements m infos env' ss
            leave_block infos env' decls env
        | Expression e ->
            let (env, _) = evaluate_expression m infos env e
            env
        | VarAssign (str, e) -> // For now, we don't check the types
            let (env, res) = evaluate_expression m infos env e
            let v' = Map.add str res env.v
            { env with v=v' }
        | FunAssign (str, lst, e) -> // For now, we don't check the types
            let (env, lst) = evaluate_expressions m infos env lst
            let (env, res) = evaluate_expression m infos env e
            let f' = Map.add (str, lst) res env.f
            { env with f=f' }
        | ForallFunAssign (str, hes, v) -> // For now, we don't check the types
            let compute_value_for (env:Model.Environment) exprs uvars acc inst =
                let value = eval_value_with m infos env v (List.map (fun (v:VarDecl) -> v.Name) uvars) inst
                let args = reconstruct_hexpression hes exprs inst
                Map.add (str,args) value acc
            let (exprs, uvars) = separate_hexpression hes
            let (env, exprs) = evaluate_expressions m infos env exprs
            let possibilities = List.map (fun d -> d.Type) uvars
            let possibilities = Model.all_values_ext infos possibilities
            let res = Seq.fold (compute_value_for env exprs uvars) Map.empty possibilities
            let f' = Map.fold (fun acc k v -> Map.add k v acc) env.f res
            { env with f=f' }
        | IfElse (e, sif, selse) ->
            let (env, v) = evaluate_expression m infos env e
            match v with
            | ConstBool true -> execute_statement m infos env sif
            | ConstBool false | _ -> execute_statement m infos env selse
        | IfSomeElse (decl, v, sif, selse) ->
            match if_some_value m infos env decl v with
            | Some value ->
                let env' = enter_new_block infos env [decl] [Some value]
                let env' = execute_statement m infos env' sif
                leave_block infos env' [decl] env
            | None ->
                execute_statement m infos env selse
        | Assert v ->
            if evaluate_value m infos env v = ConstBool true then env
            else raise (AssertionFailed (env, v))

    and execute_statements (m:ModuleDecl) infos (env:Model.Environment) ss =
        let aux env s =
            execute_statement m infos env s
        List.fold aux env ss
    
    and execute_inline_action infos (env:Model.Environment) input output (effect:Model.Environment->Model.Environment) args =
        let env' = enter_new_block infos env (output::input) (None::(List.map (fun a -> Some a) args))
        let env' = effect env'
        let res =
            match Map.tryFind output.Name env'.v with
            | None -> ConstVoid
            | Some cv -> cv
        (leave_block infos env' (output::input) env, res)

    and execute_action (m:ModuleDecl) infos (env:Model.Environment) action args = // For now, we don't check the types
        let action_decl = find_action m action
        let effect env = execute_statement m infos env action_decl.Content
        execute_inline_action infos env action_decl.Args action_decl.Output effect args

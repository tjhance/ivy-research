module TInterpreter

    open MinimalAST
    open Trace

    type ModuleDecl = ModuleDecl<Model.TypeInfos,Model.Environment>

    let rec trace_statement (m:ModuleDecl) infos (env:Model.Environment) s =
        match s with
        | AtomicGroup (sts) ->
            let trs = trace_statements m infos env sts
            TrAtomicGroup((env, final_env_of_trs trs env, are_fully_executed trs), trs)
        | NewBlock (decls, ss) ->
            let env' = Interpreter.enter_new_block infos env decls (List.map (fun _ -> None) decls)
            let trs = trace_statements m infos env' ss
            let env' = final_env_of_trs trs env'
            let env' = Interpreter.leave_block infos env' decls env
            let rd = (env, env', are_fully_executed trs)
            TrNewBlock (rd, decls, trs)
        | VarAssign (str, v) ->
            let env' = Interpreter.execute_statement m infos env (VarAssign (str,v))
            let rd = (env, env', true)
            TrVarAssign (rd, str, v)
        | VarAssignAction (name, action, vs) ->
            trace_action m infos env action vs name
        | FunAssign (str, ds, v) ->
            let env' = Interpreter.execute_statement m infos env (FunAssign (str,ds,v))
            let rd = (env, env', true)
            TrFunAssign (rd, str, ds, v)
        | IfElse (v, sif, selse) ->
            let cv = Interpreter.evaluate_value m infos env v
            let tr =
                match cv with
                | AST.ConstBool true -> trace_statement m infos env sif
                | AST.ConstBool false -> trace_statement m infos env selse
                | _ -> raise Interpreter.TypeError
            let rd = (env, final_env tr, is_fully_executed tr)
            TrIfElse (rd, v, tr)
        | IfSomeElse (decl, v, sif, selse) ->
            match Interpreter.if_some_value m infos env decl v with
            | Some value ->
                let env' = Interpreter.enter_new_block infos env [decl] [Some value]
                let tr = trace_statement m infos env' sif
                let env' = final_env tr
                let env' = Interpreter.leave_block infos env' [decl] env
                let rd = (env, env', is_fully_executed tr)
                TrIfSomeElse (rd, Some value, decl, v, tr)
            | None ->
                let tr = trace_statement m infos env selse
                let env' = final_env tr
                let rd = (env, env', is_fully_executed tr)
                TrIfSomeElse (rd, None, decl, v, tr)
        | Assert v ->
             if Interpreter.evaluate_value m infos env v = AST.ConstBool true
             then TrAssert ((env, env, true), v)
             else TrAssert ((env, env, false), v)
        | Assume v ->
             if Interpreter.evaluate_value m infos env v = AST.ConstBool true
             then TrAssume ((env, env, true), v)
             else TrAssume ((env, env, false), v)

    and trace_statements (m:ModuleDecl) infos (env:Model.Environment) ss =
        let rec aux env ss =
            match ss with
            | [] -> []
            | s::ss ->
                let tr = trace_statement m infos env s
                if is_fully_executed tr
                then tr::(aux (final_env tr) ss)
                else [tr]
        aux env ss

    and trace_inline_action (m:ModuleDecl) infos (env:Model.Environment) input output (effect:Model.Environment->TrStatement) vs assigned_var_name =
        let cvs = Interpreter.evaluate_values m infos env vs
        let env' = Interpreter.enter_new_block infos env (output::input) (None::(List.map (fun a -> Some a) cvs))
        let tr = effect env'
        let env' = final_env tr

        let res =
            if is_fully_executed tr
            then
                match Map.tryFind output.Name env'.v with
                | None -> Some (AST.type_default_value output.Type)
                | Some cv -> Some cv
            else None

        let env' = Interpreter.leave_block infos env' (output::input) env

        let rd =
            match res with
            | None -> (env, env', false)
            | Some cv ->
                (env, Interpreter.execute_statement m infos env' (VarAssign (assigned_var_name,ValueConst cv)), true)

        TrVarAssignAction (rd, assigned_var_name, input, output, vs, tr)

    and trace_action (m:ModuleDecl) infos (env:Model.Environment) name args assigned_var_name =
        let action_decl = find_action m name
        let effect env = trace_statement m infos env action_decl.Content
        trace_inline_action m infos env action_decl.Args action_decl.Output effect args assigned_var_name

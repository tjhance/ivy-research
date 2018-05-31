module TInterpreter

    open AST
    open Trace

    let rec trace_expression (m:ModuleDecl) infos (env:Model.Environment) e =
        let apply_op env es op =
            let trs = trace_expressions m infos env es
            let last_env = final_env_of_exprs trs env
            let retval =
                if exprs_are_fully_evaluated trs
                then
                    let rets = List.map ret_value_of_expr trs
                    Some (op last_env rets)
                else None
            let red = (env, last_env, retval)
            (red, trs)
        let binary_op env e1 e2 op =
            let op _ lst =
                let (a,b) = Helper.lst_to_couple lst
                op a b
            let (red,lst) = apply_op env [e1;e2] op
            let (t1,t2) = Helper.lst_to_couple lst
            (red, t1, t2)
        let unary_op env e op =
            let op _ lst =
                op (List.head lst)
            let (red,lst) = apply_op env [e] op
            (red, List.head lst)
        match e with
        | ExprConst cv ->
            let red = (env,env,Some cv)
            TrExprConst (red, cv)
        | ExprVar v ->
            let red = (env,env,Some (Interpreter.evaluate_value infos env (ValueVar v)))
            TrExprVar (red, v)
        | ExprFun (str, lst) ->
            let eval last_env cvs =
                let cvs = List.map (fun cv -> ValueConst cv) cvs
                Interpreter.evaluate_value infos last_env (ValueFun (str, cvs))
            let (red, trs) = apply_op env lst eval
            TrExprFun (red, str, trs)
        | ExprAction (str, lst) ->
            trace_action m infos env str lst
        | ExprEqual (e1, e2) ->
            let eval cv1 cv2 =
                ConstBool (Interpreter.value_equal infos cv1 cv2)
            TrExprEqual (binary_op env e1 e2 eval)
        | ExprOr (e1, e2) ->
            TrExprOr (binary_op env e1 e2 Interpreter.value_or)
        | ExprAnd (e1, e2) ->
            TrExprAnd (binary_op env e1 e2 Interpreter.value_and)
        | ExprNot e ->
            TrExprNot (unary_op env e Interpreter.value_not)
        | ExprSomeElse (d,f,e) ->
            let red = (env,env,Some (Interpreter.evaluate_value infos env (ValueSomeElse (d,f,e))))
            TrExprSomeElse (red,d,f,e)

    and trace_expressions (m:ModuleDecl) infos (env:Model.Environment) es =
        let aux trs e =
            match trs with
            | [] -> [trace_expression m infos env e]
            | hd::_ ->
                if expr_is_fully_evaluated hd
                then
                    let env = final_env_of_expr hd
                    (trace_expression m infos env e)::trs
                else (TrExprNotEvaluated)::trs
        List.rev (List.fold aux [] es)

    and trace_statement (m:ModuleDecl) infos (env:Model.Environment) s =
        let apply_op env es op =
            let tr_es = trace_expressions m infos env es
            let env' = final_env_of_exprs tr_es env
            let (env',b) =
                if exprs_are_fully_evaluated tr_es
                then
                    let rets = List.map ret_value_of_expr tr_es
                    let env' = op env' rets
                    (env', true)
                else (env', false)
            let rsd = (env, env', b)
            (rsd, tr_es)
        let apply_unary_op env e op =
            let op env lst =
                op env (List.head lst)
            let (rsd,lst) = apply_op env [e] op
            (rsd, List.head lst)
        match s with
        | NewBlock (decls, ss) ->
            let env' = Interpreter.enter_new_block infos env decls (List.map (fun _ -> None) decls)
            let trs = trace_statements m infos env' ss
            let env' = final_env_of_sts trs env'
            let env' = Interpreter.leave_block infos env' decls env
            let rsd = (env, env', sts_are_fully_executed trs)
            TrNewBlock (rsd, decls, trs)
        | Expression e ->
            let tr = trace_expression m infos env e
            let env' = final_env_of_exprs [tr] env
            let rsd = (env, env', expr_is_fully_evaluated tr)
            TrExpression (rsd, tr)
        | VarAssign (str, e) ->
            let op (env:Model.Environment) cv =
                let v' = Map.add str cv env.v
                { env with v=v' }
            let (rsd, tr_e) = apply_unary_op env e op
            TrVarAssign (rsd, str, tr_e)
        | FunAssign (str, lst, e) ->
            let op (env:Model.Environment) cvs =
                let (cvs, cv) = Helper.separate_last cvs
                let f' = Map.add (str, cvs) cv env.f
                { env with f=f' }
            let (rsd, tr_es) = apply_op env (lst@[e]) op
            let (tr_es, tr_e) = Helper.separate_last tr_es
            TrFunAssign (rsd, str, tr_es, tr_e)
        | ForallFunAssign (str, hes, v) ->
            let (exprs, uvars) = Interpreter.separate_hexpression hes
            let op (env:Model.Environment) cvs =
                let exprs = List.map (fun cv -> Expr (ExprConst cv)) cvs
                let uvars = List.map Hole uvars
                let args = Interpreter.reconstruct_hexpression hes exprs uvars
                Interpreter.execute_statement m infos env (ForallFunAssign (str,args,v))
            let (rsd, tr_es) = apply_op env exprs op
            let tr_es = List.map TrExpr tr_es
            let uvars = List.map TrHole uvars
            let args = Interpreter.reconstruct_hexpression hes tr_es uvars
            TrForallFunAssign (rsd, str, args, v)
        | IfElse (e, sif, selse) ->
            let tr = trace_expression m infos env e
            let env' = final_env_of_exprs [tr] env
            let (env',tr_st) =
                if expr_is_fully_evaluated tr
                then
                    let ret = ret_value_of_expr tr
                    match ret with
                    | ConstBool true ->
                        let tr_st = trace_statement m infos env' sif
                        let env' = final_env_of_st tr_st
                        (env', tr_st)
                    | ConstBool false | _ ->
                        let tr_st = trace_statement m infos env' selse
                        let env' = final_env_of_st tr_st
                        (env', tr_st)
                else (env', TrNotEvaluated)
            let rsd = (env, env', st_is_fully_executed tr_st)
            TrIfElse (rsd, tr, tr_st)
        | IfSomeElse (decl, f, sif, selse) ->
            match Interpreter.if_some_value infos env decl f with
            | Some value ->
                let env' = Interpreter.enter_new_block infos env [decl] [Some value]
                let tr = trace_statement m infos env' sif
                let env' = final_env_of_sts [tr] env'
                let env' = Interpreter.leave_block infos env' [decl] env
                let rsd = (env, env', st_is_fully_executed tr)
                TrIfSomeElse (rsd, Some value, decl, f, tr)
            | None ->
                let tr = trace_statement m infos env selse
                let env' = final_env_of_sts [tr] env
                let rsd = (env, env', st_is_fully_executed tr)
                TrIfSomeElse (rsd, None, decl, f, tr)
        | Assert f ->
             if Interpreter.evaluate_formula infos env f
             then
                let rsd = (env, env, true)
                TrAssert (rsd, f)
             else
                let rsd = (env, env, false)
                TrAssert (rsd, f)

    and trace_statements (m:ModuleDecl) infos (env:Model.Environment) ss =
        let rec aux env ss =
            match ss with
            | [] -> []
            | s::ss ->
                let tr = trace_statement m infos env s
                if st_is_fully_executed tr
                then
                    let env = final_env_of_st tr
                    tr::(aux env ss)
                else [tr]
        aux env ss

    and trace_inline_action (m:ModuleDecl) infos (env:Model.Environment) input output (effect:Model.Environment->TrStatement) args =
        let tr_args = trace_expressions m infos env args
        let env' = final_env_of_exprs tr_args env
        if exprs_are_fully_evaluated tr_args
        then
            let args = List.map ret_value_of_expr tr_args
            let env'' = Interpreter.enter_new_block infos env' (output::input) (None::(List.map (fun a -> Some a) args))
            let tr = effect env''
            let env'' = final_env_of_sts [tr] env''

            let res =
                if st_is_fully_executed tr
                then
                    match Map.tryFind output.Name env''.v with
                    | None -> Some ConstVoid
                    | Some cv -> Some cv
                else None

            let env'' = Interpreter.leave_block infos env'' (output::input) env'
            let red = (env, env'', res)
            TrExprAction (red, input, output, tr_args, tr)
        else
            let red = (env, env', None)
            TrExprAction (red, input, output, tr_args, TrNotEvaluated)

    and trace_action (m:ModuleDecl) infos (env:Model.Environment) name args =
        let action_decl = find_action m name
        let effect env = trace_statement m infos env action_decl.Content
        trace_inline_action m infos env action_decl.Args action_decl.Output effect args
module TInterpreter

    open AST
    open Trace

    exception ExprAssertionFailed of TrExpression * Formula
    exception StAssertionFailed of TrStatement * Formula

    let rec trace_expression (m:ModuleDecl) infos (env:Model.Environment) e =
        let apply_op es op =
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
        let binary_op e1 e2 op =
            let op _ lst =
                let (a,b) = Helper.lst_to_couple lst
                op a b
            let (red,lst) = apply_op [e1;e2] op
            let (t1,t2) = Helper.lst_to_couple lst
            (red, t1, t2)
        let unary_op e op =
            let op _ lst =
                op (List.head lst)
            let (red,lst) = apply_op [e] op
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
            let (red, trs) = apply_op lst eval
            TrExprFun (red, str, trs)
        | ExprAction (str, lst) ->
            trace_action m infos env str lst
        | ExprEqual (e1, e2) ->
            let eval cv1 cv2 =
                ConstBool (Interpreter.value_equal infos cv1 cv2)
            TrExprEqual (binary_op e1 e2 eval)
        | ExprOr (e1, e2) ->
            TrExprOr (binary_op e1 e2 Interpreter.value_or)
        | ExprAnd (e1, e2) ->
            TrExprAnd (binary_op e1 e2 Interpreter.value_and)
        | ExprNot e ->
            TrExprNot (unary_op e Interpreter.value_not)
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
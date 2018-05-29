module TInterpreter

    open AST
    open Trace

    exception ExprAssertionFailed of TrExpression * Formula
    exception StAssertionFailed of TrStatement * Formula

    let rec trace_expression (m:ModuleDecl) infos (env:Model.Environment) e =
        match e with
        | ExprConst cv ->
            let red = (env,env,Some cv)
            TrExprConst (red, cv)
        | ExprVar v ->
            let red = (env,env,Some (Interpreter.evaluate_value infos env (ValueVar v)))
            TrExprVar (red, v)
        | ExprFun (str, lst) ->
            let lst = trace_expressions m infos env lst
            let last_env = final_env_of_exprs lst env
            let retval =
                if exprs_are_fully_evaluated lst
                then
                    let rets = List.map ret_value_of_expr lst
                    let rets = List.map (fun cv -> ValueConst cv) rets
                    Some (Interpreter.evaluate_value infos last_env (ValueFun (str, rets)))
                else None
            let red = (env, last_env, retval)
            TrExprFun (red, str, lst)

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

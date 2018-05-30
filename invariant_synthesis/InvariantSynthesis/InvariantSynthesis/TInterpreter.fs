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
            let lst = trace_expressions m infos env lst
            let last_env = final_env_of_exprs lst env
            trace_action m infos last_env str lst
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


    and trace_action (m:ModuleDecl) infos (env:Model.Environment) name trargs =
        TrExprNotEvaluated// TODO
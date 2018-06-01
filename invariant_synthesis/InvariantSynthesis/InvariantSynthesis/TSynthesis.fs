module TSynthesis

    open AST
    open Trace
    open TInterpreter
    open Interpreter
    open System

    let marks_for_value = Synthesis.marks_for_value
    let marks_for_formula = Synthesis.marks_for_formula
    let config_union = Synthesis.config_union
    let is_var_marked = Synthesis.is_var_marked
    let config_enter_block = Synthesis.config_enter_block
    let config_leave_block = Synthesis.config_leave_block
    let is_better_config = Synthesis.is_better_config

    let rec marks_before_expression module_decl infos tr cfg mark_value =
        match tr with
        | TrExprNotEvaluated _ -> cfg
        | TrExprConst _ -> cfg
        | TrExprVar ((env,_,v), str) ->
            let (_, cfg') = marks_for_value infos env Set.empty (ValueVar str)
            if mark_value && v <> None then (config_union cfg cfg') else cfg
        | TrExprFun ((_,env',v), str, tr_es) ->
            let cfg =
                if mark_value && v <> None then
                    let vs = List.map ret_value_of_expr tr_es
                    let (_, cfg') = marks_for_value infos env' Set.empty (ValueFun (str, List.map (fun v -> ValueConst v) vs))
                    config_union cfg cfg'
                else cfg
            marks_before_expressions module_decl infos tr_es cfg (List.map (fun _ -> mark_value) tr_es)
        | TrExprAction ((_,_,v), input, output, tr_es, tr_st) ->
            let (cfg, args_marks) =
                if exprs_are_fully_evaluated tr_es
                then
                    let (m,um,ad) = config_enter_block infos cfg (output::input)
                    let m =
                        if mark_value && v <> None then
                            { m with v = Set.add output.Name m.v }
                        else m
                    let (m,um,ad) = marks_before_statement module_decl infos tr_st (m,um,ad)
                    let args_marks = List.map (is_var_marked infos (m,um,ad)) (List.map (fun (decl:VarDecl) -> decl.Name) input)
                    let cfg = config_leave_block infos (m,um,ad) (output::input) cfg
                    (cfg, args_marks)
                else (cfg, List.map (fun _ -> false) tr_es)
            marks_before_expressions module_decl infos tr_es cfg args_marks
        | TrExprEqual ((_,env',v), tr_e1, tr_e2) ->
            let cfg =
                if mark_value && v <> None then
                    let v1 = ret_value_of_expr tr_e1
                    let v2 = ret_value_of_expr tr_e2
                    let (_, cfg') = marks_for_formula infos env' Set.empty (Equal (ValueConst v1,ValueConst v2))
                    config_union cfg cfg'
                else cfg
            marks_before_expressions module_decl infos [tr_e1;tr_e2] cfg [mark_value;mark_value]
        | TrExprOr ((_,_,v), tr_e1, tr_e2) ->
            let aux mark1 mark2 =
                marks_before_expressions module_decl infos [tr_e1;tr_e2] cfg [mark1;mark2]
            if mark_value && v <> None then
                let v1 = ret_value_of_expr tr_e1
                let v2 = ret_value_of_expr tr_e2
                match v1, v2 with
                | ConstBool true, ConstBool false -> aux true false
                | ConstBool false, ConstBool true -> aux false true
                | ConstBool true, ConstBool true -> 
                    let cfg1 = aux true false
                    let cfg2 = aux false true
                    if is_better_config cfg2 cfg1 then cfg2 else cfg1
                | ConstBool false, ConstBool false | _, _ -> aux true true
            else aux false false
        | TrExprAnd ((env,env',cv), tr_e1, tr_e2) ->
            let (env1,env1',v1) = runtime_data_of_expr tr_e1
            let tr_not_e1 = TrExprNot ((env1,env1',Option.map value_not v1), tr_e1)
            let (env2,env2',v2) = runtime_data_of_expr tr_e2
            let tr_not_e2 = TrExprNot ((env2,env2',Option.map value_not v2), tr_e2)
            let tr_or = TrExprOr ((env, env', Option.map value_not cv), tr_not_e1, tr_not_e2)
            marks_before_expression module_decl infos (TrExprNot ((env,env',cv), tr_or)) cfg mark_value
        | TrExprNot (_,tr) -> marks_before_expression module_decl infos tr cfg mark_value
        | TrExprSomeElse ((env,_,rv),_,d,f,v) ->
            if mark_value && rv <> None
            then
                let (_,cfg') = marks_for_value infos env Set.empty (ValueSomeElse (d,f,v))
                config_union cfg cfg'
            else cfg

    // Expressions are analysed in reverse order
    and marks_before_expressions module_decl infos trs cfg mark_values =
        let aux cfg tr_e mark =
            marks_before_expression module_decl infos tr_e cfg mark
        List.fold2 aux cfg (List.rev trs) (List.rev mark_values)

    and marks_before_statement module_decl infos tr cfg =
        Synthesis.empty_config // TODO

    and marks_before_statements module_decl infos tr cfg =
        Synthesis.empty_config // TODO

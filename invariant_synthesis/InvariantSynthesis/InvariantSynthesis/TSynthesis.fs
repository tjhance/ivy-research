module TSynthesis

    open AST
    open Trace

    let marks_for_value = Synthesis.marks_for_value
    let marks_for_formula = Synthesis.marks_for_formula
    let config_union = Synthesis.config_union
    let is_var_marked = Synthesis.is_var_marked
    let is_fun_marked = Synthesis.is_fun_marked
    let remove_var_marks = Synthesis.remove_var_marks
    let remove_fun_marks = Synthesis.remove_fun_marks
    let config_enter_block = Synthesis.config_enter_block
    let config_leave_block = Synthesis.config_leave_block
    let is_better_config = Synthesis.is_better_config
    let compute_neighbors_with_perm = Synthesis.compute_neighbors_with_perm
    let add_ineq_between = Synthesis.add_ineq_between

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
            let tr_not_e1 = TrExprNot ((env1,env1',Option.map Interpreter.value_not v1), tr_e1)
            let (env2,env2',v2) = runtime_data_of_expr tr_e2
            let tr_not_e2 = TrExprNot ((env2,env2',Option.map Interpreter.value_not v2), tr_e2)
            let tr_or = TrExprOr ((env, env', Option.map Interpreter.value_not cv), tr_not_e1, tr_not_e2)
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
        match tr with
        | TrNotEvaluated _ -> cfg
        | TrNewBlock (_, decls, tr_sts) ->
            let cfg' = config_enter_block infos cfg decls
            let cfg' = marks_before_statements module_decl infos tr_sts cfg'
            config_leave_block infos cfg' decls cfg
        | TrExpression (_, tr_e) -> marks_before_expression module_decl infos tr_e cfg false
        | TrVarAssign (_, str, tr_e) ->
            let (cfg, marked) =
                if expr_is_fully_evaluated tr_e then
                    let marked = is_var_marked infos cfg str
                    let cfg = remove_var_marks infos cfg str
                    (cfg, marked)
                else (cfg, false)
            marks_before_expression module_decl infos tr_e cfg marked
        | TrFunAssign (rsd, str, tr_es, tr_e) ->
            (*
            fun(ei)=e
            ei ---eval---> vi

            Two cases:
            fun(vi) is marked ->    We mark all ei, we add necessary inequalities, we mark e.
                                    We remove mark on fun(vi)
            otherwise ->    We mark all ei s.t. there exists wi different from ei with fun(...wi...) marked, 
                            we add necessary inequalities
            *)
            let tr_all = tr_es@[tr_e]
            if exprs_are_fully_evaluated tr_all then
                let vs = List.map ret_value_of_expr tr_es
                let marked = is_fun_marked infos cfg str vs
                let cfg = remove_fun_marks infos cfg str vs
                
                let n = List.length vs
                let permutations = Helper.all_permutations n
                let possibilities = Seq.map (compute_neighbors_with_perm infos cfg marked str vs Helper.identity Helper.identity) permutations

                let cfg = marks_before_expression module_decl infos tr_e cfg marked

                let treat_possibility (marks, neighbors) =
                    let (m,um,ad) = cfg
                    let (m,um,ad) = marks_before_expressions module_decl infos tr_es (m,um,ad) marks
                    let ad = Seq.fold2 (fun ad v ns -> add_ineq_between infos ad (Set.singleton v) ns) ad vs neighbors
                    (m,um,ad)

                let results = Seq.map treat_possibility possibilities
                Helper.seq_min is_better_config results
            else
                marks_before_expressions module_decl infos tr_all cfg (List.map (fun _ -> false) tr_all) 
        // TODO

    // Statements are analysed in reverse order
    and marks_before_statements module_decl infos trs cfg =
        let aux cfg tr =
            marks_before_statement module_decl infos tr cfg
        List.fold aux cfg trs

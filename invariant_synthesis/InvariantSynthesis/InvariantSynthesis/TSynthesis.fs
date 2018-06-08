module TSynthesis

    open AST
    open Trace

    let marks_for_value = Synthesis.marks_for_value
    let marks_for_value_with = Synthesis.marks_for_value_with
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
    let fun_marks_matching = Synthesis.fun_marks_matching
    let is_model_dependent_type = Synthesis.is_model_dependent_type

    // We rewrite some functions of Interpreter 

    let rec reconstruct_hexpression hes vs uvs =
        match hes with
        | [] -> []
        | (TrHole _)::hes -> (List.head uvs)::(reconstruct_hexpression hes vs (List.tail uvs))
        | (TrExpr _)::hes -> (List.head vs)::(reconstruct_hexpression hes (List.tail vs) uvs)

    let rec reconstruct_hexpression_opt hes vs =
        match hes with
        | [] -> []
        | (TrHole _)::hes -> None::(reconstruct_hexpression_opt hes vs)
        | (TrExpr _)::hes -> (Some (List.head vs))::(reconstruct_hexpression_opt hes (List.tail vs))

    let rec reconstruct_hexpression_opt2 hes vs =
        match hes with
        | [] -> []
        | (TrHole _)::hes -> None::(reconstruct_hexpression_opt2 hes vs)
        | (TrExpr _)::hes -> (List.head vs)::(reconstruct_hexpression_opt2 hes (List.tail vs))

    let separate_hexpression hes =
        // Fixed expressions
        let exprs = List.filter (fun he -> match he with TrHole _ -> false | TrExpr _ -> true) hes
        let exprs = List.map (fun he -> match he with TrHole _ -> failwith "" | TrExpr e -> e) exprs
        // Universally quantified vars
        let uvars = List.filter (fun he -> match he with TrHole _ -> true | TrExpr _ -> false) hes
        let uvars = List.map (fun he -> match he with TrHole d -> d | TrExpr _ -> failwith "") uvars
        (exprs, uvars)

    let rec keep_only_expr_hexpression hes res =
        match hes with
        | [] -> []
        | (TrHole _)::hes -> keep_only_expr_hexpression hes (List.tail res)
        | (TrExpr _)::hes -> (List.head res)::(keep_only_expr_hexpression hes (List.tail res))

    let rec keep_only_hole_hexpression hes res =
        match hes with
        | [] -> []
        | (TrHole _)::hes -> (List.head res)::(keep_only_hole_hexpression hes (List.tail res))
        | (TrExpr _)::hes -> keep_only_hole_hexpression hes (List.tail res)

    ////////////////////////////////////////////////////////////////////////////

    let rec marks_before_expression mdecl infos tr cfg mark_value =
        match tr with
        | TrExprNotEvaluated _ -> cfg
        | TrExprConst _ -> cfg
        | TrExprVar ((env,_,v), str) ->
            let (_, cfg') = marks_for_value mdecl infos env Set.empty (ValueVar str)
            if mark_value && v <> None then (config_union cfg cfg') else cfg
        | TrExprFun ((_,env',v), str, tr_es) ->
            let (cfg, args_mark) =
                if mark_value && v <> None then
                    let vs = List.map ret_value_of_expr tr_es
                    let (_, cfg') = marks_for_value mdecl infos env' Set.empty (ValueFun (str, List.map (fun v -> ValueConst v) vs))
                    (config_union cfg cfg', true)
                else (cfg, false)
            marks_before_expressions mdecl infos tr_es cfg (List.map (fun _ -> args_mark) tr_es)
        | TrExprAction ((_,_,v), input, output, tr_es, tr_st) ->
            let (cfg, args_marks) =
                if exprs_are_fully_evaluated tr_es
                then
                    let (m,um,ad) = config_enter_block infos cfg (output::input)
                    let m =
                        if mark_value && v <> None then
                            { m with v = Set.add output.Name m.v }
                        else m
                    let (m,um,ad) = marks_before_statement mdecl infos tr_st (m,um,ad)
                    let args_marks = List.map (is_var_marked infos (m,um,ad)) (List.map (fun (decl:VarDecl) -> decl.Name) input)
                    let cfg = config_leave_block infos (m,um,ad) (output::input) cfg
                    (cfg, args_marks)
                else (cfg, List.map (fun _ -> false) tr_es)
            marks_before_expressions mdecl infos tr_es cfg args_marks
        | TrExprMacro ((env,_,rv),str,vs) ->
            if mark_value && rv <> None
            then
                let (_,cfg') = marks_for_value mdecl infos env Set.empty (ValueMacro (str,vs))
                config_union cfg cfg'
            else cfg
        | TrExprEqual ((_,env',v), tr_e1, tr_e2) ->
            let (cfg, args_mark) =
                if mark_value && v <> None then
                    let v1 = ret_value_of_expr tr_e1
                    let v2 = ret_value_of_expr tr_e2
                    let (_, cfg') = marks_for_value mdecl infos env' Set.empty (ValueEqual (ValueConst v1,ValueConst v2))
                    (config_union cfg cfg', true)
                else (cfg, false)
            marks_before_expressions mdecl infos [tr_e1;tr_e2] cfg [args_mark;args_mark]
        | TrExprOr ((_,_,v), tr_e1, tr_e2) ->
            let aux mark1 mark2 =
                marks_before_expressions mdecl infos [tr_e1;tr_e2] cfg [mark1;mark2]
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
            marks_before_expression mdecl infos (TrExprNot ((env,env',cv), tr_or)) cfg mark_value
        | TrExprNot (_,tr) -> marks_before_expression mdecl infos tr cfg mark_value
        | TrExprSomeElse ((env,_,rv),_,d,f,v) ->
            if mark_value && rv <> None
            then
                let (_,cfg') = marks_for_value mdecl infos env Set.empty (ValueSomeElse (d,f,v))
                config_union cfg cfg'
            else cfg
        | TrExprExists ((env,_,rv),d,v) ->
            if mark_value && rv <> None
            then
                let (_,cfg') = marks_for_value mdecl infos env Set.empty (ValueExists (d,v))
                config_union cfg cfg'
            else cfg
        | TrExprForall ((env,_,rv),d,v) ->
            if mark_value && rv <> None
            then
                let (_,cfg') = marks_for_value mdecl infos env Set.empty (ValueForall (d,v))
                config_union cfg cfg'
            else cfg
        | TrExprImply ((env,env',cv), tr_e1, tr_e2) ->
            let (env1,env1',v1) = runtime_data_of_expr tr_e1
            let tr_not_e1 = TrExprNot ((env1,env1',Option.map Interpreter.value_not v1), tr_e1)
            let tr_or = TrExprOr ((env, env', cv), tr_not_e1, tr_e2)
            marks_before_expression mdecl infos tr_or cfg mark_value

    // Expressions are analysed in reverse order
    and marks_before_expressions module_decl infos trs cfg mark_values =
        let aux cfg tr_e mark =
            marks_before_expression module_decl infos tr_e cfg mark
        List.fold2 aux cfg (List.rev trs) (List.rev mark_values)

    and marks_before_statement mdecl infos tr cfg =
        match tr with
        | TrNotEvaluated _ -> cfg
        | TrNewBlock (_, decls, tr_sts) ->
            let cfg' = config_enter_block infos cfg decls
            let cfg' = marks_before_statements mdecl infos tr_sts cfg'
            config_leave_block infos cfg' decls cfg
        | TrExpression (_, tr_e) -> marks_before_expression mdecl infos tr_e cfg false
        | TrVarAssign ((_,_,b), str, tr_e) ->
            let (cfg, marked) =
                if b then
                    let marked = is_var_marked infos cfg str
                    let cfg = remove_var_marks infos cfg str
                    (cfg, marked)
                else (cfg, false)
            marks_before_expression mdecl infos tr_e cfg marked
        | TrFunAssign ((_,_,b), str, tr_es, tr_e) ->
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
            if b then
                let vs = List.map ret_value_of_expr tr_es
                let marked = is_fun_marked infos cfg str vs
                let cfg = remove_fun_marks infos cfg str vs
                
                let n = List.length vs
                let permutations = Helper.all_permutations n
                let possibilities = Seq.map (compute_neighbors_with_perm infos cfg marked str vs Helper.identity Helper.identity) permutations

                let cfg = marks_before_expression mdecl infos tr_e cfg marked

                let treat_possibility (marks, neighbors) =
                    let (m,um,ad) = cfg
                    let (m,um,ad) = marks_before_expressions mdecl infos tr_es (m,um,ad) marks
                    let ad = Seq.fold2 (fun ad v ns -> add_ineq_between infos ad (Set.singleton v) ns) ad vs neighbors
                    (m,um,ad)

                let results = Seq.map treat_possibility possibilities
                Helper.seq_min is_better_config results
            else
                marks_before_expressions mdecl infos tr_all cfg (List.map (fun _ -> false) tr_all)
        | TrForallFunAssign ((env,_,b), str, tr_hes, v) ->
            (*
            fun (ei,Xi) = V(Xi)
            ei ---eval---> vi

            Two cases:
            Nothing marked ->   restrict ei as usual
            Some values marked in m or um ->    restrict all ei

            Foreach value marked in m:
                remove mark for value in m
                restrict V(Xi) for corresponding values of Xi (no uvar)
            Foreach value marked in um:
                remove mark for value in um
                restrict V(Xi) for corresponding values of Xi (with X in uvar)

            We add necessary inequalities.
            *)
            let (tr_es, uvars) = separate_hexpression tr_hes
            if b then
                let vs = List.map ret_value_of_expr tr_es
                let m_marks = fun_marks_matching infos cfg str (reconstruct_hexpression_opt tr_hes vs)
                let um_marks = fun_marks_matching infos cfg str (reconstruct_hexpression_opt tr_hes vs)
                let all_marks = Set.union m_marks um_marks
                let marked = not (Set.isEmpty all_marks)
                let cfg = Set.fold (fun cfg (_,vs) -> remove_fun_marks infos cfg str vs) cfg all_marks

                let n = List.length vs
                let permutations = Helper.all_permutations n
                let transform = reconstruct_hexpression_opt2 tr_hes
                let inv_trans = keep_only_expr_hexpression tr_hes
                let expr_possibilities = Seq.map (compute_neighbors_with_perm infos cfg marked str vs transform inv_trans) permutations
            
                let compute_marks_for (env:Model.Environment) v unames model_dependent hole_vs =
                    let uvars =
                        if model_dependent
                        then
                            let md_decls = Set.filter (fun (d:VarDecl) -> is_model_dependent_type d.Type) (Set.ofList unames)
                            Set.map (fun (d:VarDecl) -> d.Name) md_decls
                        else Set.empty
                    marks_for_value_with mdecl infos env uvars v (List.map (fun (d:VarDecl) -> d.Name) unames) hole_vs
                let add_marks_for_all (env:Model.Environment) v uvars model_dependent hole_vss cfg =
                    let aux acc hole_vs =
                        let (_,cfg) = compute_marks_for env v uvars model_dependent hole_vs
                        config_union acc cfg
                    Set.fold aux cfg hole_vss

                let final_env = final_env_of_exprs tr_es env
                // m_marks
                let m_marks = Set.map (fun (_,vs) -> keep_only_hole_hexpression tr_hes vs) m_marks
                let cfg = add_marks_for_all final_env v uvars false m_marks cfg
                // um_marks
                let um_marks = Set.map (fun (_,vs) -> keep_only_hole_hexpression tr_hes vs) um_marks
                let cfg = add_marks_for_all final_env v uvars true um_marks cfg

                let treat_possibility (marks, neighbors) =
                    let (m,um,ad) = cfg
                    // exprs
                    let (m, um, ad) = marks_before_expressions mdecl infos tr_es (m, um, ad) marks
                    let ad = Seq.fold2 (fun ad v ns -> add_ineq_between infos ad (Set.singleton v) ns) ad vs neighbors
                    (m,um,ad)

                let results = Seq.map treat_possibility expr_possibilities
                Helper.seq_min is_better_config results
            else
                marks_before_expressions mdecl infos tr_es cfg (List.map (fun _ -> false) tr_es)
        | TrIfElse (_, tr_e, tr_st) ->
            let cfg =
                if expr_is_fully_evaluated tr_e then
                    marks_before_statement mdecl infos tr_st cfg
                else cfg
            marks_before_expression mdecl infos tr_e cfg true
        | TrIfSomeElse ((env,_,_), cv, decl, v, tr_s) ->
            match cv with
            | Some _ ->
                let cfg' = config_enter_block infos cfg [decl]
                let cfg' = marks_before_statement mdecl infos tr_s cfg'
                let (_, cfg'') =
                    if is_var_marked infos cfg' decl.Name
                    then marks_for_value mdecl infos (initial_env_of_st tr_s) Set.empty v
                    (* NOTE: In the case above, we may also ensure that every other value doesn't satisfy the predicate.
                       However, it is a different problem than garanteeing the invariant value,
                       since we are bound to an execution (maybe there is no uniqueness in this execution).
                       Therefore, we suppose that the choice made is always the value we choose here (if it satisfies the condition).
                       An assertion can also be added by the user to ensure this uniqueness. *)
                    else marks_for_value mdecl infos env Set.empty (ValueExists (decl, v))
                let cfg' = config_union cfg' cfg''
                config_leave_block infos cfg' [decl] cfg
            | None ->
                let cfg = marks_before_statement mdecl infos tr_s cfg
                let (_,cfg') = marks_for_value mdecl infos env Set.empty (ValueNot (ValueExists (decl, v)))
                config_union cfg cfg'
        | TrAssert ((env,_,_),v) ->
            let (_, cfg') = marks_for_value mdecl infos env Set.empty v
            config_union cfg cfg'

    // Statements are analysed in reverse order
    and marks_before_statements module_decl infos trs cfg =
        let aux cfg tr =
            marks_before_statement module_decl infos tr cfg
        List.fold aux cfg trs

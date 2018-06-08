module Synthesis

    open AST
    open Interpreter

    type FunMarks = Set<string * List<ConstValue>>
    type VarMarks = Set<string>

    type Marks = { f : FunMarks; v : VarMarks }

    type DiffConstraint = Set<ConstValue * ConstValue> // Small improvement of the result: we don't impose inequality if (we are sure) it is unecessary

    type AdditionalData = { d : DiffConstraint; md : bool } // md means model-dependent

    let empty_marks = { f = Set.empty; v = Set.empty }
    let empty_ad = { d = Set.empty; md = false }
    let empty_config = (empty_marks, empty_marks, empty_ad)
    // A config (m,um,ad) is composed of alist of marks m, a list of model-dependent marks um, additional data ad

    let is_model_dependent_type t =
        match t with
        | Void -> false
        | Bool -> false
        | Uninterpreted _ -> true

    let is_model_dependent_value cv =
        match cv with
        | ConstVoid -> false
        | ConstBool _ -> false
        | ConstInt _ -> true

    let marks_count m =
        (Set.count m.f) + (Set.count m.v)

    let marks_reduce op1 op2 ms : Marks =
        let fs = Seq.map (fun m -> m.f) ms
        let vs = Seq.map (fun m -> m.v) ms
        { f = op1 fs ; v = op2 vs }

    let ad_reduce op1 op2 ads : AdditionalData =
        let ds = Seq.map (fun ad -> ad.d) ads
        let mds = Seq.map (fun ad -> ad.md) ads
        { d = op1 ds ; md = op2 mds }
    
    let marks_union_many = marks_reduce Set.unionMany Set.unionMany    
    let marks_union m1 m2 = marks_union_many ([m1;m2] |> List.toSeq)
    let marks_diff m1 m2 =
        { f=Set.difference m1.f m2.f ; v=Set.difference m1.v m2.v }

    let ad_union_many = ad_reduce Set.unionMany (Seq.exists (fun e -> e))
    let ad_union ad1 ad2 = ad_union_many ([ad1;ad2] |> List.toSeq)

    let config_union (m1,um1,ad1) (m2,um2,ad2) =
        (marks_union m1 m2, marks_union um1 um2, ad_union ad1 ad2)

    let config_union_many configs =
        Seq.fold (fun cfg1 cfg2 -> config_union cfg1 cfg2) empty_config configs

    let is_better_config (m1, um1, ad1) (m2, um2, ad2) =
        if not ad1.md && ad2.md
        then true
        else if ad1.md && not ad2.md
        then false
        else if marks_count um1 < marks_count um2
        then true
        else if marks_count um1 > marks_count um2
        then false
        else if marks_count m1 < marks_count m2
        then true
        else if marks_count m1 > marks_count m2
        then false
        else if Set.count ad1.d < Set.count ad2.d
        then true
        else false

    let add_diff_constraint _ ad cv1 cv2 =
        let d' = Set.add (cv1, cv2) ad.d
        let d' = Set.add (cv2, cv1) d'
        { ad with d=d' }

    let is_var_marked _ (m, um, _) var =
        (Set.contains var m.v) || (Set.contains var um.v)
    
    let remove_var_marks _ (m, um, ad) var : Marks * Marks * AdditionalData =
        ({m with v = Set.remove var m.v}, {um with v = Set.remove var um.v}, ad)

    exception InvalidOperation
    let bool_of_cv cv =
        match cv with
        | ConstBool b -> b
        | _ -> failwith "Boolean value expected."

    // uvar: variables that can browse an arbitrary large range (depending on the model)
    let rec marks_for_value mdecl infos env uvar v : ConstValue * (Marks * Marks * AdditionalData) =
        match v with
        | ValueConst c -> (c, empty_config)
        | ValueVar str ->
            let eval = evaluate_value mdecl infos env (ValueVar str)
            if Set.contains str uvar
            then (eval, (empty_marks, { empty_marks with v=Set.singleton str }, { empty_ad with md=true }))
            else (eval, ({ empty_marks with v=Set.singleton str }, empty_marks, empty_ad))
        | ValueFun (str, values) ->
            let res = List.map (marks_for_value mdecl infos env uvar) values
            let (cvs, cfgs) = List.unzip res
            let (m,um,ad) = config_union_many cfgs
            let vs = List.map (fun cv -> ValueConst cv) cvs
            let eval = evaluate_value mdecl infos env (ValueFun (str, vs))
            if ad.md
            then
                (eval, (m, { um with f = Set.add (str, cvs) um.f }, ad))
            else
                (eval, ({ m with f = Set.add (str, cvs) m.f }, um, ad))
        | ValueMacro (str, values) ->
            let macro = find_macro mdecl str
            let dico = List.fold2 (fun acc (d:VarDecl) v -> Map.add d.Name v acc) Map.empty macro.Args values
            let v = map_vars_in_value (macro.Value) dico
            marks_for_value mdecl infos env uvar v
        | ValueEqual (v1, v2) ->
            let (cv1, cfg1) = marks_for_value mdecl infos env uvar v1
            let (cv2, cfg2) = marks_for_value mdecl infos env uvar v2
            let (m,um,ad) = config_union cfg1 cfg2
            if value_equal infos cv1 cv2 then (ConstBool true, (m, um, ad))
            else (ConstBool false, (m, um, add_diff_constraint infos ad cv1 cv2))
        | ValueOr (v1, v2) ->
            let (cv1, cfg1) = marks_for_value mdecl infos env uvar v1
            let (cv2, cfg2) = marks_for_value mdecl infos env uvar v2
            match cv1, cv2 with
            | ConstBool false, ConstBool false -> (ConstBool false, config_union cfg1 cfg2)
            | ConstBool true, ConstBool false -> (ConstBool true, cfg1)
            | ConstBool false, ConstBool true -> (ConstBool true, cfg2)
            | ConstBool true, ConstBool true when is_better_config cfg2 cfg1 -> (ConstBool true, cfg2)
            | ConstBool true, ConstBool true -> (ConstBool true, cfg1)
            | _, _ -> (ConstVoid, config_union cfg1 cfg2)
        | ValueAnd (v1, v2) ->
            marks_for_value mdecl infos env uvar (ValueNot (ValueOr (ValueNot v1, ValueNot v2)))
        | ValueNot v ->
            let (cv,cfg) = marks_for_value mdecl infos env uvar v
            (value_not cv, cfg)
        | ValueSomeElse (d,f,v) ->
            match if_some_value mdecl infos env d f with
            | Some cv ->
                (* NOTE: See note for IfSomeElse statement. *)
                let is_uvar = is_model_dependent_type d.Type && not (Set.isEmpty uvar) 
                let uvar = if is_uvar then Set.add d.Name uvar else uvar
                let (_,cfg) = marks_for_value_with mdecl infos env uvar f [d.Name] [cv]
                (cv,cfg)
            | None -> 
                let (_,cfg1) = marks_for_value mdecl infos env uvar (ValueNot (ValueExists (d,f)))
                let (cv,cfg2) = marks_for_value mdecl infos env uvar v
                (cv, config_union cfg1 cfg2)
        | ValueForall (decl, v) ->
            let is_uvar = 
                is_model_dependent_type decl.Type && 
                (not (Set.isEmpty uvar) || evaluate_value mdecl infos env (ValueForall (decl, v)) = ConstBool true)
            let uvar = if is_uvar then Set.add decl.Name uvar else uvar
            let values = Model.all_values infos decl.Type
            let all_possibilities = Seq.map (fun cv -> marks_for_value_with mdecl infos env uvar v [decl.Name] [cv]) values
            if Seq.forall (fun (b,_) -> b = ConstBool true) all_possibilities
            then
                // We mix all contraints (some will probably be model-dependent)
                (ConstBool true, config_union_many (Seq.map (fun (_,cfg) -> cfg) all_possibilities))
            else
                // We pick one constraint that breaks the forall
                let possibilities = Seq.filter (fun (b, _) -> b = ConstBool false) all_possibilities
                let possibilities = Seq.map (fun (_,cfg) -> cfg) possibilities
                let cfg = Helper.seq_min is_better_config possibilities
                (ConstBool false, cfg)
        | ValueExists (decl, v) ->
            marks_for_value mdecl infos env uvar (ValueNot (ValueForall (decl, ValueNot v)))
        | ValueImply (v1, v2) ->
            marks_for_value mdecl infos env uvar (ValueOr (ValueNot v1, v2))

    and marks_for_value_with mdecl infos (env:Model.Environment) uvar v names values =
        let v' = List.fold2 (fun acc n v -> Map.add n v acc) env.v names values
        let (v, cfg) = marks_for_value mdecl infos {env with v=v'} uvar v
        (v, List.fold (remove_var_marks infos) cfg names)

    // env: initial environment (before the execution of the expressions)
    // Returns the final environment
    // Returns the list of each environment before the execution of an expression, IN THE REVERSE ORDER
    // Also returns the values of the expressions (in the expressions order)
    let intermediate_environments module_decl infos env es =
        let aux (envs, vs) e =
            let (h, v) = evaluate_expression module_decl infos (List.head envs) e
            (h::envs, v::vs)
        let (envs, vs) = (List.fold aux ([env], []) es)
        (List.head envs, List.tail envs, List.rev vs)

    let intermediate_environments_st module_decl infos env sts =
        let aux envs st =
            let h = execute_statement module_decl infos (List.head envs) st
            (h::envs)
        let envs = (List.fold aux [env] sts)
        (List.head envs, List.tail envs)

    let config_leave_block _ (m,um,ad) lvars (old_m,old_um,_) =
        let marks_leave_block m old_m : Marks =
            let rollback acc (decl:VarDecl) =
                if Set.contains decl.Name old_m.v
                then Set.add decl.Name acc
                else Set.remove decl.Name acc
            { m with v=List.fold rollback m.v lvars }
        (marks_leave_block m old_m, marks_leave_block um old_um, ad)

    let config_enter_block _ (m,um,ad) lvars =
        let marks_enter_block m : Marks =
            let rm acc (decl:VarDecl) = Set.remove decl.Name acc
            { m with v=List.fold rm m.v lvars }
        (marks_enter_block m, marks_enter_block um, ad)

    let is_fun_marked _ (m, um, _) str vs =
        Set.contains (str, vs) m.f || Set.contains (str, vs) um.f
    
    let remove_fun_marks _ (m, um, ad) str vs : Marks * Marks * AdditionalData =
        ({m with f = Set.remove (str,vs) m.f}, {um with f = Set.remove (str,vs) um.f}, ad)

    let fun_marks_matching infos (m,um,_) str ovs =
        let aux m : FunMarks =
            let value_match v dv =
                match dv with
                | None -> true
                | Some dv -> value_equal infos v dv
            let match_pattern fm =
                match fm with
                | (s, _) when s<>str -> false
                | (_, lst) -> List.forall2 value_match lst ovs
            (Set.filter match_pattern m.f)
        Set.union (aux m) (aux um)

    // Used in fun assign statements
    let compute_neighbors_with_perm infos cfg marked str vs transform inv_trans permut =
        let f = Helper.permutation_to_fun permut
        let inv_f = Helper.permutation_to_fun (Helper.inv_permutation permut)
        let n = List.length vs
        let vs = List.permute f vs
        // acc: i, constraints, neighbors list
        let aux (i, prev_constraints, nlist) v =
            let real_i = inv_f i
            let neighbors = fun_marks_matching infos cfg str (transform prev_constraints)
            let neighbors = Set.map (fun (_, l) -> List.item real_i (inv_trans l)) neighbors
            let neighbors = Set.remove v neighbors
            let marked = marked || not (Set.isEmpty neighbors)

            let constr = if marked then Some v else None
            let new_constraints = Helper.list_set real_i constr prev_constraints
            let new_nlist = Helper.list_set real_i neighbors nlist
            (i+1, new_constraints, new_nlist)
        let (_,cs,ns) = List.fold aux (0, List.init n (fun _ -> None), List.init n (fun _ -> Set.empty)) vs
        (List.map (fun c -> c <> None) cs, ns)

    let add_ineq_between infos ad cvs1 cvs2 =
        let aux infos cvs ad cv =
            Set.fold (fun ad cv' -> add_diff_constraint infos ad cv cv') ad cvs
        Set.fold (aux infos cvs1) ad cvs2

    // env: initial environment (before the execution of the expr)
    // m, um: marks after the execution of the expr
    let rec marks_before_expression mdecl infos env expr cfg mark_value =
        match expr with
        | ExprConst _ -> cfg
        | ExprVar str ->
            let (_, cfg') = marks_for_value mdecl infos env Set.empty (ValueVar str)
            if mark_value then (config_union cfg cfg') else cfg
        | ExprFun (str, es) ->
            let (env, envs, vs) = intermediate_environments mdecl infos env es
            let (_, cfg') = marks_for_value mdecl infos env Set.empty (ValueFun (str, List.map (fun v -> ValueConst v) vs))
            let cfg = if mark_value then (config_union cfg cfg') else cfg
            marks_before_expressions mdecl infos envs (List.rev es) cfg (List.map (fun _ -> mark_value) es)
        | ExprAction (str, es) ->
            let (env, envs, lst) = intermediate_environments mdecl infos env es
            let (args_marks, cfg) = marks_before_action mdecl infos env str lst cfg mark_value
            marks_before_expressions mdecl infos envs (List.rev es) cfg (List.rev args_marks)
        | ExprMacro (str, vs) ->
            if mark_value
            then
                let (_,cfg') = marks_for_value mdecl infos env Set.empty (ValueMacro (str,vs))
                config_union cfg cfg'
            else cfg
        | ExprEqual (e1, e2) ->
            let (env1, v1) = evaluate_expression mdecl infos env e1
            let (env2, v2) = evaluate_expression mdecl infos env1 e2
            let (_, cfg') = marks_for_value mdecl infos env2 Set.empty (ValueEqual (ValueConst v1,ValueConst v2))
            let cfg = if mark_value then (config_union cfg cfg') else cfg
            let cfg = marks_before_expression mdecl infos env1 e2 cfg mark_value
            marks_before_expression mdecl infos env e1 cfg mark_value
        | ExprOr (e1, e2) ->
            let (env1, v1) = evaluate_expression mdecl infos env e1
            let (_, v2) = evaluate_expression mdecl infos env1 e2
            let aux mark1 mark2 =
                let cfg' = marks_before_expression mdecl infos env1 e2 cfg (mark_value && mark2)
                marks_before_expression mdecl infos env e1 cfg' (mark_value && mark1)
            match v1, v2 with
            | ConstBool true, ConstBool false -> aux true false
            | ConstBool false, ConstBool true -> aux false true
            | ConstBool true, ConstBool true -> 
                let cfg1 = aux true false
                let cfg2 = aux false true
                if is_better_config cfg2 cfg1 then cfg2 else cfg1
            | ConstBool false, ConstBool false | _, _ -> aux true true
        | ExprAnd (e1, e2) -> marks_before_expression mdecl infos env (ExprNot (ExprOr (ExprNot e1, ExprNot e2))) cfg mark_value
        | ExprNot e -> marks_before_expression mdecl infos env e cfg mark_value
        | ExprSomeElse (d,f,v) ->
            if mark_value
            then
                let (_,cfg') = marks_for_value mdecl infos env Set.empty (ValueSomeElse (d,f,v))
                config_union cfg cfg'
            else cfg
        | ExprExists (d,v) ->
            if mark_value
            then
                let (_,cfg') = marks_for_value mdecl infos env Set.empty (ValueExists (d,v))
                config_union cfg cfg'
            else cfg
        | ExprForall (d,v) ->
            if mark_value
            then
                let (_,cfg') = marks_for_value mdecl infos env Set.empty (ValueForall (d,v))
                config_union cfg cfg'
            else cfg
        | ExprImply (e1, e2) -> marks_before_expression mdecl infos env (ExprOr (ExprNot e1, e2)) cfg mark_value

    // envs: the env before each expression
    and marks_before_expressions module_decl infos envs es cfg mark_values =
        let aux cfg (env, e) mark =
            marks_before_expression module_decl infos env e cfg mark
        List.fold2 aux cfg (List.zip envs es) mark_values

    and marks_before_statement mdecl infos env st cfg =
        match st with
        | NewBlock (decls, sts) ->
            let env' = enter_new_block infos env decls (List.map (fun _ -> None) decls)
            let cfg' = config_enter_block infos cfg decls
            let (_, envs) = intermediate_environments_st mdecl infos env' sts
            let cfg' = marks_before_statements mdecl infos envs (List.rev sts) cfg'
            config_leave_block infos cfg' decls cfg
        | Expression e -> marks_before_expression mdecl infos env e cfg false
        | VarAssign (str, e) ->
            let marked = is_var_marked infos cfg str
            let cfg = remove_var_marks infos cfg str
            marks_before_expression mdecl infos env e cfg marked
        | FunAssign (str, es, e) ->
            (*
            fun(ei)=e
            ei ---eval---> vi

            Two cases:
            fun(vi) is marked ->    We mark all ei, we add necessary inequalities, we mark e.
                                    We remove mark on fun(vi)
            otherwise ->    We mark all ei s.t. there exists wi different from ei with fun(...wi...) marked, 
                            we add necessary inequalities
            *)
            let (env, envs, vs) = intermediate_environments mdecl infos env es
            let marked = is_fun_marked infos cfg str vs
            let cfg = remove_fun_marks infos cfg str vs

            let n = List.length vs
            let permutations = Helper.all_permutations n
            let possibilities = Seq.map (compute_neighbors_with_perm infos cfg marked str vs Helper.identity Helper.identity) permutations

            let cfg = marks_before_expression mdecl infos env e cfg marked

            let treat_possibility (marks, neighbors) =
                let (m,um,ad) = cfg
                let (m,um,ad) = marks_before_expressions mdecl infos envs (List.rev es) (m,um,ad) (List.rev marks)
                let ad = Seq.fold2 (fun ad v ns -> add_ineq_between infos ad (Set.singleton v) ns) ad vs neighbors
                (m,um,ad)

            let results = Seq.map treat_possibility possibilities
            Helper.seq_min is_better_config results
        | ForallFunAssign (str, hes, v) ->
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
            let (es, uvars) = separate_hexpression hes
            let (env, envs, vs) = intermediate_environments mdecl infos env es
            let m_marks = fun_marks_matching infos cfg str (reconstruct_hexpression_opt hes vs)
            let um_marks = fun_marks_matching infos cfg str (reconstruct_hexpression_opt hes vs)
            let all_marks = Set.union m_marks um_marks
            let marked = not (Set.isEmpty all_marks)
            let cfg = Set.fold (fun cfg (_,vs) -> remove_fun_marks infos cfg str vs) cfg all_marks

            let n = List.length vs
            let permutations = Helper.all_permutations n
            let transform = reconstruct_hexpression_opt2 hes
            let inv_trans = keep_only_expr_hexpression hes
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

            // m_marks
            let m_marks = Set.map (fun (_,vs) -> keep_only_hole_hexpression hes vs) m_marks
            let cfg = add_marks_for_all env v uvars false m_marks cfg
            // um_marks
            let um_marks = Set.map (fun (_,vs) -> keep_only_hole_hexpression hes vs) um_marks
            let cfg = add_marks_for_all env v uvars true um_marks cfg

            let treat_possibility (marks, neighbors) =
                let (m,um,ad) = cfg
                // exprs
                let (m, um, ad) = marks_before_expressions mdecl infos envs (List.rev es) (m, um, ad) (List.rev marks)
                let ad = Seq.fold2 (fun ad v ns -> add_ineq_between infos ad (Set.singleton v) ns) ad vs neighbors
                (m,um,ad)

            let results = Seq.map treat_possibility expr_possibilities
            Helper.seq_min is_better_config results
        | IfElse (e, sif, selse) ->
            let (env', v) = evaluate_expression mdecl infos env e
            let cfg =
                match v with
                | ConstBool true -> marks_before_statement mdecl infos env' sif cfg
                | ConstBool false | _ -> marks_before_statement mdecl infos env' selse cfg
            marks_before_expression mdecl infos env e cfg true
        | IfSomeElse (decl, v, sif, selse) ->
            match if_some_value mdecl infos env decl v with
            | Some value ->
                let env' = enter_new_block infos env [decl] [Some value]
                let cfg' = config_enter_block infos cfg [decl]
                let cfg' = marks_before_statement mdecl infos env' sif cfg'
                let (_, cfg'2) =
                    if is_var_marked infos cfg' decl.Name
                    then marks_for_value mdecl infos env' Set.empty v
                    (* NOTE: In the case above, we may also ensure that every other value doesn't satisfy the predicate.
                       However, it is a different problem than garanteeing the invariant value,
                       since we are bound to an execution (maybe there is no uniqueness in this execution).
                       Therefore, we suppose that the choice made is always the value we choose here (if it satisfies the condition).
                       An assertion can also be added by the user to ensure this uniqueness. *)
                    else marks_for_value mdecl infos env Set.empty (ValueExists (decl, v))
                let cfg' = config_union cfg' cfg'2
                config_leave_block infos cfg' [decl] cfg
            | None ->
                 let cfg1 = marks_before_statement mdecl infos env selse cfg
                 let (_, cfg2) = marks_for_value mdecl infos env Set.empty (ValueNot (ValueExists (decl, v)))
                 config_union cfg1 cfg2
        | Assert v ->
            let (_, cfg') = marks_for_value mdecl infos env Set.empty v
            config_union cfg cfg'
            
    // envs: the env before each statement
    and marks_before_statements module_decl infos envs sts cfg =
        let aux cfg env st =
            marks_before_statement module_decl infos env st cfg
        List.fold2 aux cfg envs sts

    and marks_before_inline_action infos (env:Model.Environment) input output effect args cfg mark_value =
        let env' = enter_new_block infos env (output::input) (None::(List.map (fun a -> Some a) args))
        let (m',um',ad') = config_enter_block infos cfg (output::input)
        let m' =
            if mark_value then
                { m' with v = Set.add output.Name m'.v }
            else m'
        let (m', um', ad') = effect env' (m',um',ad')
        let args_marks = List.map (is_var_marked infos (m',um',ad')) (List.map (fun (decl:VarDecl) -> decl.Name) input)
        let cfg = config_leave_block infos (m',um',ad') (output::input) cfg
        (args_marks, cfg)

    and marks_before_action (mdecl:ModuleDecl) infos env action args cfg mark_value =
        let action_decl = find_action mdecl action
        let effect env cfg = marks_before_statement mdecl infos env action_decl.Content cfg
        marks_before_inline_action infos env action_decl.Args action_decl.Output effect args cfg mark_value
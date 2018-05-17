module Synthesis

    open AST
    open Interpreter

    // TODO: simplify code by adding a config_union function

    type FunMarks = Set<string * List<ConstValue>>
    type VarMarks = Set<string>

    type Marks = { f : FunMarks; v : VarMarks }

    type DiffConstraint = Set<ConstValue * ConstValue> // Small improvement of the result: we don't impose inequality if (we are sure) it is unecessary

    type AdditionalData = { d : DiffConstraint; md : bool } // md means model-dependent

    let empty_marks = { f = Set.empty; v = Set.empty }

    let empty_ad = { d = Set.empty; md = false }

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

    let marks_map op1 op2 ms : Marks =
        let fs = Seq.map (fun m -> m.f) ms
        let vs = Seq.map (fun m -> m.v) ms
        { f = op1 fs ; v = op2 vs }

    let ad_map op1 op2 ads : AdditionalData =
        let ds = Seq.map (fun ad -> ad.d) ads
        let mds = Seq.map (fun ad -> ad.md) ads
        { d = op1 ds ; md = op2 mds }
    
    let marks_union_many = marks_map Set.unionMany Set.unionMany    
    let marks_inter_many = marks_map Set.intersectMany Set.intersectMany
    let marks_union m1 m2 = marks_union_many ([m1;m2] |> List.toSeq)
    let marks_inter m1 m2 = marks_inter_many ([m1;m2] |> List.toSeq)
    let marks_diff m1 m2 =
        { f = Set.difference m1.f m2.f ; v = Set.difference m1.v m2.v }

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

    let add_diff_constraint infos ad cv1 cv2 =
        let d' = Set.add (cv1, cv2) ad.d
        let d' = Set.add (cv2, cv1) d'
        { ad with d=d' }

    let ad_union_many = ad_map Set.unionMany (Seq.exists (fun e -> e))
    let ad_union ad1 ad2 = ad_union_many ([ad1;ad2] |> List.toSeq)

    let unzip4 lst =
        let rec aux lst (acc1,acc2,acc3,acc4) =
            match lst with
            | [] -> (List.rev acc1,List.rev acc2,List.rev acc3,List.rev acc4)
            | (h1,h2,h3,h4)::lst -> aux lst (h1::acc1,h2::acc2,h3::acc3,h4::acc4)
        aux lst ([],[],[],[])

    exception InvalidOperation
    let bool_of_cv cv =
        match cv with
        | ConstBool b -> b
        | _ -> failwith "Boolean value expected."

    // uvar: variables that can browse an arbitrary large range (depending on the model)
    let rec marks_for_value infos env uvar v : ConstValue * Marks * Marks * AdditionalData =
        match v with
        | ValueConst c -> (c, empty_marks, empty_marks, empty_ad)
        | ValueVar str ->
            if Set.contains str uvar
            then (evaluate_value infos env (ValueVar str), empty_marks, { empty_marks with v=Set.singleton str }, { empty_ad with md=true })
            else (evaluate_value infos env (ValueVar str), { empty_marks with v=Set.singleton str }, empty_marks, empty_ad)
        | ValueFun (str, values) ->
            let res = List.map (marks_for_value infos env uvar) values
            let (cvs, ms, ums, ads) = unzip4 res
            let m = marks_union_many ms
            let um = marks_union_many ums
            let ad = ad_union_many ads
            let vs = List.map (fun cv -> ValueConst cv) cvs
            if ad.md
            then
                (evaluate_value infos env (ValueFun (str, vs)), m, { um with f = Set.add (str, cvs) um.f }, ad)
            else
                (evaluate_value infos env (ValueFun (str, vs)), { m with f = Set.add (str, cvs) m.f }, um, ad)
        | ValueEqual (v1, v2) ->
            let (cv1, m1, um1, ad1) = marks_for_value infos env uvar v1
            let (cv2, m2, um2, ad2) = marks_for_value infos env uvar v2
            let m = marks_union m1 m2
            let um = marks_union um1 um2
            let ad = ad_union ad1 ad2
            if value_equal infos cv1 cv2 then (ConstBool true, m, um, ad)
            else (ConstBool false, m, um, add_diff_constraint infos ad cv1 cv2)
        | ValueOr (v1, v2) ->
            let (cv1, m1, um1, ad1) = marks_for_value infos env uvar v1
            let (cv2, m2, um2, ad2) = marks_for_value infos env uvar v2
            match cv1, cv2 with
            | ConstBool false, ConstBool false -> (ConstBool false, marks_union m1 m2, marks_union um1 um2, ad_union ad1 ad2)
            | ConstBool true, ConstBool false -> (ConstBool true, m1, um1, ad1)
            | ConstBool false, ConstBool true -> (ConstBool true, m2, um2, ad2)
            | ConstBool true, ConstBool true when is_better_config (m2, um2, ad2) (m1, um1, ad1) -> (ConstBool true, m2, um2, ad2)
            | ConstBool true, ConstBool true -> (ConstBool true, m1, um1, ad1)
            | _, _ -> (ConstVoid, marks_union m1 m2, marks_union um1 um2, ad_union ad1 ad2)
        | ValueAnd (v1, v2) ->
            marks_for_value infos env uvar (ValueNot (ValueOr (ValueNot v1, ValueNot v2)))
        | ValueNot v ->
            let (cv,m,um,ad) = marks_for_value infos env uvar v
            (value_not cv, m, um, ad)
        | ValueSomeElse (d,f,v) ->
            match if_some_value infos env d f with
            | Some v ->
                (* NOTE: See note for IfSomeElse statement. *)
                let is_uvar = is_model_dependent_type d.Type && not (Set.isEmpty uvar) 
                let uvar = if is_uvar then Set.add d.Name uvar else uvar
                let (_,m,um,ad) = marks_for_formula_with infos env uvar f d.Name v
                (v,m,um,ad)
            | None -> 
                let (_,m,um,ad) = marks_for_formula infos env uvar (Not (Exists (d,f)))
                let (v,m2,um2,ad2) = marks_for_value infos env uvar v
                (v, marks_union m m2, marks_union um um2, ad_union ad ad2)
    
    // uvar: variables that can browse an arbitrary large range (depending on the model)
    // Return type : (formula value, important elements, universally quantified important elements (depend on the model) )
    and marks_for_formula infos env uvar f : bool * Marks * Marks * AdditionalData =
        match f with
        | Const  b -> (b, empty_marks, empty_marks, empty_ad)
        | Equal (v1, v2) ->
            let (cv, m, um, ad) = marks_for_value infos env uvar (ValueEqual (v1, v2))
            (bool_of_cv cv, m, um, ad)
        | Or (f1, f2) ->
            let (b1, m1, um1, ad1) = marks_for_formula infos env uvar f1
            let (b2, m2, um2, ad2) = marks_for_formula infos env uvar f2
            match b1, b2 with
            | false, false -> (false, marks_union m1 m2, marks_union um1 um2, ad_union ad1 ad2)
            | true, false -> (true, m1, um1, ad1)
            | false, true -> (true, m2, um2, ad2)
            | true, true when is_better_config (m2, um2, ad2) (m1, um1, ad1) -> (true, m2, um2, ad2)
            | true, true -> (true, m1, um1, ad1)
        | And (f1, f2) ->
            marks_for_formula infos env uvar (Not (Or (Not f1, Not f2)))
        | Not f ->
            let (b,m,um,ad) = marks_for_formula infos env uvar f
            (not b, m, um, ad)
        | Forall (decl, f) ->
            let is_uvar = 
                is_model_dependent_type decl.Type && 
                (not (Set.isEmpty uvar) || evaluate_formula infos env (Forall (decl, f)))
            let uvar = if is_uvar then Set.add decl.Name uvar else uvar
            let values = Model.all_values infos decl.Type
            let all_possibilities = Seq.map (marks_for_formula_with infos env uvar f decl.Name) values
            if Seq.forall (fun (b,_,_,_) -> b) all_possibilities
            then
                // We mix all contraints (some will probably be model-dependent)
                let ms = Seq.map (fun (_,m,_,_) -> m) all_possibilities
                let ums = Seq.map (fun (_,_,um,_) -> um) all_possibilities
                let ads = Seq.map (fun (_,_,_,ad) -> ad) all_possibilities
                (true, marks_union_many ms, marks_union_many ums, ad_union_many ads)
            else
                // We pick one constraint that breaks the forall
                let possibilities = Seq.filter (fun (b, _, _, _) -> not b) all_possibilities
                let possibilities = Seq.map (fun (_,a,b,c) -> (a,b,c)) possibilities
                let (m, um, ad) = Helper.seq_min is_better_config possibilities
                (false, m, um, ad)
        | Exists (decl, f) ->
            marks_for_formula infos env uvar (Not (Forall (decl, Not f)))

    and marks_for_formula_with infos (env:Model.Environment) uvar f name value =
        let env' = { env with v=Map.add name value env.v }
        let (b, m, um, ad) = marks_for_formula infos env' uvar f
        let m = { m with v = Set.remove name m.v }
        let um = { um with v = Set.remove name um.v }
        (b, m, um, ad)

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

    let marks_leave_block infos m lvars old_m : Marks =
        let rollback acc (decl:VarDecl) =
            if Set.contains decl.Name old_m.v
            then Set.add decl.Name acc
            else Set.remove decl.Name acc
        { m with v=List.fold rollback m.v lvars }

    let marks_leave_block2 infos m um lvars old_m old_um =
        (marks_leave_block infos m lvars old_m, marks_leave_block infos um lvars old_um)

    let marks_enter_block infos m lvars : Marks =
        let rm acc (decl:VarDecl) = Set.remove decl.Name acc
        { m with v=List.fold rm m.v lvars }

    let marks_enter_block2 infos m um lvars =
        (marks_enter_block infos m lvars, marks_enter_block infos um lvars)

    let is_var_marked infos m um var =
        (Set.contains var m.v) || (Set.contains var um.v)
    
    let remove_var_marks infos m um var : Marks * Marks =
        ({m with v = Set.remove var m.v}, {um with v = Set.remove var um.v})

    let is_fun_marked infos m str vs =
        Set.contains (str, vs) m.f

    let is_fun_marked2 infos m um str vs =
        (is_fun_marked infos m str vs) || (is_fun_marked infos um str vs)
    
    let remove_fun_marks infos m um str vs : Marks * Marks =
        ({m with f = Set.remove (str,vs) m.f}, {um with f = Set.remove (str,vs) um.f})

    let fun_marks_matching infos m str ovs : FunMarks =
        let value_match v dv =
            match dv with
            | None -> true
            | Some dv -> value_equal infos v dv
        let match_pattern fm =
            match fm with
            | (s, _) when s<>str -> false
            | (_, lst) -> List.forall2 value_match lst ovs
        (Set.filter match_pattern m.f)

    let fun_marks_matching2 infos m um str ovs =
        Set.union (fun_marks_matching infos m str ovs) (fun_marks_matching infos um str ovs)

    // Used in fun assign statements
    // Returns: list of (marked, neighbors)
    let compute_neighbors_with_perm infos m um marked str vs transform inv_trans permut =
        let f = Helper.permutation_to_fun permut
        let inv_f = Helper.permutation_to_fun (Helper.inv_permutation permut)
        let n = List.length vs
        let vs = List.permute f vs
        // acc: i, constraints, neighbors list
        let aux (i, prev_constraints, nlist) v =
            let real_i = inv_f i
            let neighbors = fun_marks_matching2 infos m um str (transform prev_constraints)
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
    // Return type : (important elements, universally quantified important elements (depend on the model))
    let rec marks_before_expression module_decl infos env expr m um ad mark_value =
        match expr with
        | ExprConst _ -> (m, um, ad)
        | ExprVar str ->
            let (_, m',um',ad') = marks_for_value infos env Set.empty (ValueVar str)
            if mark_value then (marks_union m m', marks_union um um', ad_union ad ad') else (m,um,ad)
        | ExprFun (str, es) ->
            let (env, envs, vs) = intermediate_environments module_decl infos env es
            let (_, m',um',ad') = marks_for_value infos env Set.empty (ValueFun (str, List.map (fun v -> ValueConst v) vs))
            let (m,um,ad) = if mark_value then (marks_union m m', marks_union um um', ad_union ad ad') else (m,um,ad)
            marks_before_expressions module_decl infos envs (List.rev es) m um ad (List.map (fun _ -> mark_value) es)
        | ExprAction (str, es) ->
            let (env, envs, lst) = intermediate_environments module_decl infos env es
            let (args_marks, m, um, ad) = marks_before_action module_decl infos env str lst m um ad mark_value
            marks_before_expressions module_decl infos envs (List.rev es) m um ad (List.rev args_marks)
        | ExprEqual (e1, e2) ->
            let (env1, v1) = evaluate_expression module_decl infos env e1
            let (env2, v2) = evaluate_expression module_decl infos env1 e2
            let (_, m', um', ad') = marks_for_formula infos env2 Set.empty (Equal (ValueConst v1,ValueConst v2))
            let (m, um, ad) = if mark_value then (marks_union m m', marks_union um um', ad_union ad ad') else (m, um, ad)
            let (m, um, ad) = marks_before_expression module_decl infos env1 e2 m um ad mark_value
            marks_before_expression module_decl infos env e1 m um ad mark_value
        | ExprOr (e1, e2) ->
            let (env1, v1) = evaluate_expression module_decl infos env e1
            let (_, v2) = evaluate_expression module_decl infos env1 e2
            let aux mark1 mark2 =
                let (m, um, ad) = marks_before_expression module_decl infos env1 e2 m um ad (mark_value && mark2)
                marks_before_expression module_decl infos env e1 m um ad (mark_value && mark1)
            match v1, v2 with
            | ConstBool true, ConstBool false -> aux true false
            | ConstBool false, ConstBool true -> aux false true
            | ConstBool true, ConstBool true -> 
                let (m1, um1, ad1) = aux true false
                let (m2, um2, ad2) = aux false true
                if is_better_config (m2, um2, ad2) (m1, um1, ad1) then (m2, um2, ad2) else (m1, um1, ad1)
            | ConstBool false, ConstBool false | _, _ -> aux true true
        | ExprAnd (e1, e2) -> marks_before_expression module_decl infos env (ExprNot (ExprOr (ExprNot e1, ExprNot e2))) m um ad mark_value
        | ExprNot e -> marks_before_expression module_decl infos env e m um ad mark_value
        | ExprSomeElse (d,f,e) ->
            match if_some_value infos env d f with
            | Some _ ->
                (* NOTE: See note for IfSomeElse statement. *)
                let (m2,um2,ad2) =
                    if mark_value
                    then
                        let (_,m2,um2,ad2) = marks_for_value infos env Set.empty (ValueSomeElse (d,f,ValueConst ConstVoid))
                        (m2,um2,ad2)
                    else
                        let (_,m2,um2,ad2) = marks_for_formula infos env Set.empty (Exists (d,f))
                        (m2,um2,ad2)
                (marks_union m m2, marks_union um um2, ad_union ad ad2)
            | None -> 
                let (_,m2,um2,ad2) = marks_for_formula infos env Set.empty (Not (Exists (d,f)))
                let (m,um,ad) = marks_before_expression module_decl infos env e m um ad mark_value
                (marks_union m m2, marks_union um um2, ad_union ad ad2)

    // envs: the env before each expression
    and marks_before_expressions module_decl infos envs es m um ad mark_values =
        let aux (m, um, ad) (env, e) mark =
            marks_before_expression module_decl infos env e m um ad mark
        let (m, um, ad) = List.fold2 aux (m, um, ad) (List.zip envs es) mark_values
        (m, um, ad)

    and marks_before_statement module_decl infos env st m um ad =
        match st with
        | NewBlock (decls, sts) ->
            let env' = enter_new_block infos env decls (List.map (fun _ -> None) decls)
            let (m', um') = marks_enter_block2 infos m um decls
            let (_, envs) = intermediate_environments_st module_decl infos env' sts
            let (m', um', ad) = marks_before_statements module_decl infos envs (List.rev sts) m' um' ad
            let (m', um') = marks_leave_block2 infos m' um' decls m um
            (m', um', ad)
        | Expression e -> marks_before_expression module_decl infos env e m um ad false
        | VarAssign (str, e) ->
            let marked = is_var_marked infos m um str
            let (m, um) = remove_var_marks infos m um str
            marks_before_expression module_decl infos env e m um ad marked
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
            let (env', _) = evaluate_expression module_decl infos env e
            let (_, envs, vs) = intermediate_environments module_decl infos env' es
            let marked = is_fun_marked2 infos m um str vs
            let (m, um) = remove_fun_marks infos m um str vs

            let n = List.length vs
            let permutations = Helper.all_permutations n
            let possibilities = Seq.map (compute_neighbors_with_perm infos m um marked str vs Helper.identity Helper.identity) permutations

            let treat_possibility (marks, neighbors) =
                let ad = Seq.fold2 (fun ad v ns -> add_ineq_between infos ad (Set.singleton v) ns) ad vs neighbors
                let (m, um, ad) = marks_before_expressions module_decl infos envs (List.rev es) m um ad (List.rev marks)
                marks_before_expression module_decl infos env e m um ad marked

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
            let (_, envs, vs) = intermediate_environments module_decl infos env es
            let m_marks = fun_marks_matching infos m str (reconstruct_hexpression_opt hes vs)
            let um_marks = fun_marks_matching infos um str (reconstruct_hexpression_opt hes vs)
            let all_marks = Set.union m_marks um_marks
            let marked = Set.exists (fun (_,vs) -> is_fun_marked2 infos m um str vs) all_marks
            let (m, um) = Set.fold (fun (m, um) (_,vs) -> remove_fun_marks infos m um str vs) (m, um) all_marks

            let n = List.length vs
            let permutations = Helper.all_permutations n
            let transform = reconstruct_hexpression_opt2 hes
            let inv_trans = keep_only_expr_hexpression hes
            let expr_possibilities = Seq.map (compute_neighbors_with_perm infos m um marked str vs transform inv_trans) permutations
            
            let treat_possibility (marks, neighbors) =
                let compute_marks_for (env:Model.Environment) v uvars model_dependent hole_vs =
                    let v' = List.fold2 (fun acc (decl:VarDecl) value -> Map.add decl.Name value acc) env.v uvars hole_vs
                    let env = { env with v=v' }
                    let uvars = if model_dependent then Set.map (fun (d:VarDecl) -> d.Name) (Set.ofList uvars) else Set.empty
                    marks_for_value infos env uvars v
                let add_marks_for_all (env:Model.Environment) v uvars model_dependent hole_vss m um ad =
                    let aux (m,um,ad) hole_vs =
                        let (_,m',um',ad') = compute_marks_for env v uvars model_dependent hole_vs
                        (marks_union m m', marks_union um um', ad_union ad ad')
                    Set.fold aux (m,um,ad) hole_vss

                let ad = Seq.fold2 (fun ad v ns -> add_ineq_between infos ad (Set.singleton v) ns) ad vs neighbors
                let (m, um, ad) = marks_before_expressions module_decl infos envs (List.rev es) m um ad (List.rev marks)
                // m_marks
                let m_marks = Set.map (fun (_,vs) -> keep_only_hole_hexpression hes vs) m_marks
                let (m, um, ad) = add_marks_for_all env v uvars false m_marks m um ad
                // um_marks
                let um_marks = Set.map (fun (_,vs) -> keep_only_hole_hexpression hes vs) um_marks
                let (m, um, ad) = add_marks_for_all env v uvars true um_marks m um ad
                (m,um,ad)

            let results = Seq.map treat_possibility expr_possibilities
            Helper.seq_min is_better_config results
        | IfElse (e, sif, selse) ->
            let (env', v) = evaluate_expression module_decl infos env e
            let (m, um, ad) =
                match v with
                | ConstBool true -> marks_before_statement module_decl infos env' sif m um ad
                | ConstBool false | _ -> marks_before_statement module_decl infos env' selse m um ad
            marks_before_expression module_decl infos env e m um ad true
        | IfSomeElse (decl, f, sif, selse) ->
            match if_some_value infos env decl f with
            | Some value ->
                let env' = enter_new_block infos env [decl] [Some value]
                let (m', um') = marks_enter_block2 infos m um [decl]
                let (m', um', ad) = marks_before_statement module_decl infos env' sif m' um' ad
                let (_, m2, um2, ad2) =
                    if is_var_marked infos m' um' decl.Name
                    then marks_for_formula infos env' Set.empty f
                    (* NOTE: In the case above, we may also ensure that every other value doesn't satisfy the predicate.
                       However, it is a different problem than garanteeing the invariant value,
                       since we are bound to an execution (maybe there is no uniqueness in this execution).
                       Therefore, we suppose that the choice made is always the value we choose here (if it satisfies the condition).
                       An assertion can also be added by the user to ensure this uniqueness. *)
                    else marks_for_formula infos env Set.empty (Exists (decl, f))
                let (m', um', ad) = (marks_union m' m2, marks_union um' um2, ad_union ad ad2)
                let (m', um') = marks_leave_block2 infos m' um' [decl] m um
                (m', um', ad)
            | None ->
                 let (m, um, ad) = marks_before_statement module_decl infos env selse m um ad
                 let (_, m2, um2, ad2) = marks_for_formula infos env Set.empty (Not (Exists (decl, f)))
                 (marks_union m m2, marks_union um um2, ad_union ad ad2)
        | Assert f ->
            let (_, m2, um2, ad2) = marks_for_formula infos env Set.empty f
            (marks_union m m2, marks_union um um2, ad_union ad ad2)
            
    // envs: the env before each statement
    and marks_before_statements module_decl infos envs sts m um ad =
        let aux (m, um, ad) env st =
            marks_before_statement module_decl infos env st m um ad
        List.fold2 aux (m, um, ad) envs sts

    and marks_before_inline_action infos (env:Model.Environment) input output effect args m um ad mark_value =
        let env' = enter_new_block infos env (output::input) (None::(List.map (fun a -> Some a) args))
        let (m', um') = marks_enter_block2 infos m um (output::input)
        let m' =
            if mark_value then
                { m' with v = Set.add output.Name m'.v }
            else m'
        let (m', um', ad) = effect env' m' um' ad
        let args_marks = List.map (is_var_marked infos m' um') (List.map (fun (decl:VarDecl) -> decl.Name) input)
        let (m', um') = marks_leave_block2 infos m' um' (output::input) m um
        (args_marks, m', um', ad)

    and marks_before_action (mdecl:ModuleDecl) infos env action args m um ad mark_value =
        let action_decl = find_action mdecl action
        let effect env m um ad = marks_before_statement mdecl infos env action_decl.Content m um ad
        marks_before_inline_action infos env action_decl.Args action_decl.Output effect args m um ad mark_value
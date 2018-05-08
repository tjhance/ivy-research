module Synthesis

    open AST
    open Interpreter

    type FunMarks = Set<string * List<ConstValue>>
    type VarMarks = Set<string>

    type Marks = { f : FunMarks; v : VarMarks }

    type DiffConstraint = Set<ConstValue * ConstValue> // Small improvement of the result: we don't impose inequality if (we are sure) it is unecessary

    type AdditionalData = { d : DiffConstraint }

    let empty_marks = { f = Set.empty; v = Set.empty }

    let empty_ad = { d = Set.empty }

    let marks_count m =
        (Set.count m.f) + (Set.count m.v)

    let marks_map op1 op2 ms : Marks =
        let fs = Seq.map (fun m -> m.f) ms
        let vs = Seq.map (fun m -> m.v) ms
        { f = op1 fs ; v = op2 vs }

    let ad_map op1 ads : AdditionalData =
        let ds = Seq.map (fun ad -> ad.d) ads
        { d = op1 ds}
    
    let marks_union_many = marks_map Set.unionMany Set.unionMany    
    let marks_inter_many = marks_map Set.intersectMany Set.intersectMany
    let marks_union m1 m2 = marks_union_many ([m1;m2] |> List.toSeq)
    let marks_inter m1 m2 = marks_inter_many ([m1;m2] |> List.toSeq)
    let marks_diff m1 m2 =
        { f = Set.difference m1.f m2.f ; v = Set.difference m1.v m2.v }

    let are_better_marks (m1, um1) (m2, um2) =
        if marks_count um1 < marks_count um2
        then true
        else if marks_count um1 > marks_count um2
        then false
        else if marks_count m1 < marks_count m2
        then true
        else false

    let add_diff_constraint infos ad cv1 cv2 =
        let d' = Set.add (cv1, cv2) ad.d
        let d' = Set.add (cv2, cv1) d'
        { ad with d=d' }

    let ad_union_many = ad_map Set.unionMany
    let ad_union ad1 ad2 = ad_union_many ([ad1;ad2] |> List.toSeq)

    let unzip4 lst =
        let rec aux lst (acc1,acc2,acc3,acc4) =
            match lst with
            | [] -> (List.rev acc1,List.rev acc2,List.rev acc3,List.rev acc4)
            | (h1,h2,h3,h4)::lst -> aux lst (h1::acc1,h2::acc2,h3::acc3,h4::acc4)
        aux lst ([],[],[],[])

    let rec marks_for_value infos env v : ConstValue * Marks * Marks * AdditionalData =
        match v with
        | ValueConst c -> (c, empty_marks, empty_marks, empty_ad)
        | ValueVar str -> (evaluate_value env (ValueVar str), { empty_marks with v=Set.singleton str }, empty_marks, empty_ad)
        | ValueFun (str, values) ->
            let res = List.map (marks_for_value infos env) values
            let (cvs, ms, ums, ads) = unzip4 res
            let m = marks_union_many ms
            let um = marks_union_many ums
            let vs = List.map (fun cv -> ValueConst cv) cvs
            (evaluate_value env (ValueFun (str, vs)), { m with f = Set.add (str, cvs) m.f }, um, ad_union_many ads)

    // Return type : (formula value, important elements, universally quantified important elements)
    let rec marks_for_formula infos env f : bool * Marks * Marks * AdditionalData =
        match f with
        | Const  b -> (b, empty_marks, empty_marks, empty_ad)
        | Equal (v1, v2) ->
            let (cv1, m1, um1, ad1) = marks_for_value infos env v1
            let (cv2, m2, um2, ad2) = marks_for_value infos env v2
            let m = marks_union m1 m2
            let um = marks_union um1 um2
            let ad = ad_union ad1 ad2
            if value_equal infos cv1 cv2 then (true, m, um, ad)
            else
                (false, m, um, add_diff_constraint infos ad cv1 cv2)
        | Or (f1, f2) ->
            let (b1, m1, um1, ad1) = marks_for_formula infos env f1
            let (b2, m2, um2, ad2) = marks_for_formula infos env f2
            match b1, b2 with
            | false, false -> (false, marks_union m1 m2, marks_union um1 um2, ad_union ad1 ad2)
            | true, false -> (true, m1, um1, ad1)
            | false, true -> (true, m2, um2, ad2)
            | true, true when are_better_marks (m2, um2) (m1, um1) -> (true, m2, um2, ad2)
            | true, true -> (true, m1, um1, ad1)
        | And (f1, f2) ->
            marks_for_formula infos env (Not (Or (Not f1, Not f2)))
        | Not f ->
            let (b,m,um,ad) = marks_for_formula infos env f
            (not b, m, um, ad)
        | Forall (decl, f) ->
            let marks_with value =
                let env' = { env with v=Map.add decl.Name value env.v }
                let (b, m, um, ad) = marks_for_formula infos env' f
                let m = { m with v = Set.remove decl.Name m.v }
                let um = { um with v = Set.remove decl.Name um.v }
                (b, m, um, ad)
            let values = all_values infos decl.Type
            let all_possibilities = Seq.map marks_with values
            if Seq.forall (fun (b,_,_,_) -> b) all_possibilities
            then
                // Important constraints are universally quantified...
                // Common properties stay in m, other properties move to um
                let ms = Seq.map (fun (_,m,_,_) -> m) all_possibilities
                let ums = Seq.map (fun (_,_,um,_) -> um) all_possibilities
                let ads = Seq.map (fun (_,_,_,ad) -> ad) all_possibilities
                let m = marks_inter_many ms
                let um1 = marks_union_many ums
                let um2 = marks_diff (marks_union_many ms) m
                (true, m, marks_union um1 um2, ad_union_many ads)
            else
                // We pick one constraint that breaks the forall
                let possibilities = Seq.filter (fun (b, _, _, _) -> not b) all_possibilities
                let possibilities = Seq.map (fun (_,a,b,c) -> (a,b,c)) possibilities
                let min_count (mm, mum, mad) (m, um, ad) = if are_better_marks (m, um) (mm, mum) then (m, um, ad) else (mm, mum, mad)
                let (m, um, ad) = Seq.fold min_count (Seq.head possibilities) possibilities
                (false, m, um, ad)
        | Exists (decl, f) ->
            marks_for_formula infos env (Not (Forall (decl, Not f)))

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

    let is_fun_marked infos m um str vs =
        (Set.contains (str, vs) m.f) || (Set.contains (str, vs) um.f)
    
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

    // env: initial environment (before the execution of the expr)
    // m, um: marks after the execution of the expr
    // Return type : (important elements, universally quantified important elements)
    let rec marks_before_expression module_decl infos env expr m um ad mark_value =
        match expr with
        | ExprConst _ -> (m, um, ad)
        | ExprVar str ->
            let (_, m',um',ad') = marks_for_value infos env (ValueVar str)
            if mark_value then (marks_union m m', marks_union um um', ad_union ad ad') else (m,um,ad)
        | ExprFun (str, es) ->
            let (env, envs, vs) = intermediate_environments module_decl infos env es
            let (_, m',um',ad') = marks_for_value infos env (ValueFun (str, List.map (fun v -> ValueConst v) vs))
            let (m,um,ad) = if mark_value then (marks_union m m', marks_union um um', ad_union ad ad') else (m,um,ad)
            marks_before_expressions module_decl infos envs (List.rev es) m um ad (List.map (fun _ -> mark_value) es)
        | ExprAction (str, es) ->
            let (env, envs, lst) = intermediate_environments module_decl infos env es
            let (args_marks, m, um, ad) = marks_before_action module_decl infos env str lst m um ad mark_value
            marks_before_expressions module_decl infos envs (List.rev es) m um ad (List.rev args_marks)
        | ExprEqual (e1, e2) ->
            let (env1, v1) = evaluate_expression module_decl infos env e1
            let (env2, v2) = evaluate_expression module_decl infos env1 e2
            let (_, m', um', ad') = marks_for_formula infos env2 (Equal (ValueConst v1,ValueConst v2))
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
                if are_better_marks (m2, um2) (m1, um1) then (m2, um2, ad2) else (m1, um1, ad1)
            | ConstBool false, ConstBool false | _, _ -> aux true true
        | ExprAnd (e1, e2) -> marks_before_expression module_decl infos env (ExprNot (ExprOr (ExprNot e1, ExprNot e2))) m um ad mark_value
        | ExprNot e -> marks_before_expression module_decl infos env e m um ad mark_value

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
            let (env', _) = evaluate_expression module_decl infos env e
            let (_, envs, vs) = intermediate_environments module_decl infos env' es
            let marked = is_fun_marked infos m um str vs
            let (m, um) = remove_fun_marks infos m um str vs
            let neighbors = fun_marks_matching2 infos m um str (List.map (fun _ -> None) vs)
            let neighbors = List.mapi (fun i _ -> Set.map (fun (_, l) -> List.item i l) neighbors) vs
            let neighbors = List.mapi (fun i s -> Set.remove (List.item i vs) s) neighbors
            // Important values
            let marks =
                if marked
                then List.map (fun _ -> true) es
                else List.map (fun lst -> not (Set.isEmpty lst)) neighbors
            // Inequalities with neighbors
            let add_ineq_for ad cv cvs =
                Set.fold (fun ad cv' -> add_diff_constraint infos ad cv cv') ad cvs
            let ad = List.fold2 add_ineq_for ad vs neighbors
            let (m, um, ad) = marks_before_expressions module_decl infos envs (List.rev es) m um ad (List.rev marks)
            marks_before_expression module_decl infos env e m um ad marked
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
                    then marks_for_formula infos env' f
                    else marks_for_formula infos env (Exists (decl, f))
                let (m', um', ad) = (marks_union m' m2, marks_union um' um2, ad_union ad ad2)
                let (m', um') = marks_leave_block2 infos m' um' [decl] m um
                (m', um', ad)
            | None ->
                 let (m, um, ad) = marks_before_statement module_decl infos env selse m um ad
                 let (_, m2, um2, ad2) = marks_for_formula infos env (Exists (decl, f))
                 (marks_union m m2, marks_union um um2, ad_union ad ad2)
        | Assert f ->
            let (_, m2, um2, ad2) = marks_for_formula infos env f
            (marks_union m m2, marks_union um um2, ad_union ad ad2)
            
    // envs: the env before each statement
    and marks_before_statements module_decl infos envs sts m um ad =
        let aux (m, um, ad) env st =
            marks_before_statement module_decl infos env st m um ad
        List.fold2 aux (m, um, ad) envs sts

    and marks_before_action (mdecl:ModuleDecl) infos env action args m um ad mark_value =
        let action_decl = List.find (fun (adecl:ActionDecl) -> adecl.Name = action) mdecl.Actions
        let env' = enter_new_block infos env (action_decl.Output::action_decl.Args) (None::(List.map (fun a -> Some a) args))
        let (m', um') = marks_enter_block2 infos m um (action_decl.Output::action_decl.Args)
        let m' =
            if mark_value then
                { m' with v = Set.add action_decl.Output.Name m'.v }
            else m'
        let (m', um', ad) = marks_before_statement mdecl infos env' action_decl.Content m' um' ad
        let args_marks = List.map (is_var_marked infos m' um') (List.map (fun (decl:VarDecl) -> decl.Name) action_decl.Args)
        let (m', um') = marks_leave_block2 infos m' um' (action_decl.Output::action_decl.Args) m um
        (args_marks, m', um', ad)
        // TODO: Handle abstract actions
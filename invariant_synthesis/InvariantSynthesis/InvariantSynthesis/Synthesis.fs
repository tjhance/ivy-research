﻿module Synthesis

    open MinimalAST
    open Trace
    open Interpreter

    type FunMarks = Set<string * List<ConstValue>>
    type VarMarks = Set<string>
    type DiffConstraint = Set<ConstValue * ConstValue> // We don't impose disequality if is not necessary

    type Marks = { f : FunMarks; v : VarMarks; d: DiffConstraint }

    type AdditionalData = { md : bool } // md means model-dependent

    let empty_marks = { f = Set.empty; v = Set.empty ; d = Set.empty }
    let empty_ad = { md = false }
    let empty_config = (empty_marks, empty_marks, empty_ad)
    // A config (m,um,ad) is composed of alist of marks m, a list of model-dependent marks um, additional data ad

    let is_model_dependent_type t =
        match t with
        | AST.Void -> false
        | AST.Bool -> false
        | AST.Uninterpreted _ -> true

    let is_model_dependent_value cv =
        match cv with
        | AST.ConstVoid -> false
        | AST.ConstBool _ -> false
        | AST.ConstInt _ -> true

    let marks_count m =
        (Set.count m.f) + (Set.count m.v) + (Set.count m.d)

    let marks_reduce op1 op2 op3 ms : Marks =
        let fs = Seq.map (fun m -> m.f) ms
        let vs = Seq.map (fun m -> m.v) ms
        let ds = Seq.map (fun m -> m.d) ms
        { f = op1 fs ; v = op2 vs ; d = op3 ds }

    let ad_reduce op1 ads : AdditionalData =
        let mds = Seq.map (fun ad -> ad.md) ads
        { md = op1 mds }
    
    let marks_union_many = marks_reduce Set.unionMany Set.unionMany Set.unionMany
    let marks_union m1 m2 = marks_union_many ([m1;m2] |> List.toSeq)
    let marks_diff m1 m2 =
        { f=Set.difference m1.f m2.f ; v=Set.difference m1.v m2.v; d=Set.difference m1.d m2.d }

    let ad_union_many = ad_reduce (Seq.exists Helper.identity)
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
        else false

    let add_diff_constraint _ m cv1 cv2 =
        let d' = Set.add (cv1, cv2) m.d
        let d' = Set.add (cv2, cv1) d'
        { m with d=d' }

    let is_var_marked _ (m, um, _) var =
        (Set.contains var m.v) || (Set.contains var um.v)
    
    let remove_var_marks _ (m, um, ad) var : Marks * Marks * AdditionalData =
        ({m with v = Set.remove var m.v}, {um with v = Set.remove var um.v}, ad)

    exception InvalidOperation
    let bool_of_cv cv =
        match cv with
        | AST.ConstBool b -> b
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
        | ValueEqual (v1, v2) ->
            let (cv1, cfg1) = marks_for_value mdecl infos env uvar v1
            let (cv2, cfg2) = marks_for_value mdecl infos env uvar v2
            let (m,um,ad) = config_union cfg1 cfg2
            if AST.value_equal infos cv1 cv2 then (AST.ConstBool true, (m, um, ad))
            else if ad.md
            then (AST.ConstBool false, (m, add_diff_constraint infos um cv1 cv2, ad))
            else (AST.ConstBool false, (add_diff_constraint infos m cv1 cv2, um, ad))
        | ValueOr (v1, v2) ->
            let (cv1, cfg1) = marks_for_value mdecl infos env uvar v1
            let (cv2, cfg2) = marks_for_value mdecl infos env uvar v2
            match cv1, cv2 with
            | AST.ConstBool false, AST.ConstBool false -> (AST.ConstBool false, config_union cfg1 cfg2)
            | AST.ConstBool true, AST.ConstBool false -> (AST.ConstBool true, cfg1)
            | AST.ConstBool false, AST.ConstBool true -> (AST.ConstBool true, cfg2)
            | AST.ConstBool true, AST.ConstBool true when is_better_config cfg2 cfg1 -> (AST.ConstBool true, cfg2)
            | AST.ConstBool true, AST.ConstBool true -> (AST.ConstBool true, cfg1)
            | _, _ -> raise TypeError
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
                let (_,cfg1) = marks_for_value mdecl infos env uvar (ValueForall (d, ValueNot f))
                let (cv,cfg2) = marks_for_value mdecl infos env uvar v
                (cv, config_union cfg1 cfg2)
        | ValueForall (decl, v) ->
            let is_uvar = 
                is_model_dependent_type decl.Type && 
                (not (Set.isEmpty uvar) || evaluate_value mdecl infos env (ValueForall (decl, v)) = AST.ConstBool true)
            let uvar = if is_uvar then Set.add decl.Name uvar else uvar
            let values = Model.all_values infos decl.Type
            let all_possibilities = Seq.map (fun cv -> marks_for_value_with mdecl infos env uvar v [decl.Name] [cv]) values
            if Seq.forall (fun (b,_) -> b = AST.ConstBool true) all_possibilities
            then
                // We mix all contraints (some will probably be model-dependent)
                (AST.ConstBool true, config_union_many (Seq.map (fun (_,cfg) -> cfg) all_possibilities))
            else
                // We pick one constraint that breaks the forall
                let possibilities = Seq.filter (fun (b, _) -> b = AST.ConstBool false) all_possibilities
                let possibilities = Seq.map (fun (_,cfg) -> cfg) possibilities
                let cfg = Helper.seq_min is_better_config possibilities
                (AST.ConstBool false, cfg)
        | ValueInterpreted (str, vs) ->
            let res = List.map (marks_for_value mdecl infos env uvar) vs
            let (cvs, cfgs) = List.unzip res
            let cfg = config_union_many cfgs
            let eval = (find_interpreted_action mdecl str).Effect infos env cvs
            (eval, cfg)

    and marks_for_value_with mdecl infos (env:Model.Environment) uvar v names values =
        let v' = List.fold2 (fun acc n v -> Map.add n v acc) env.v names values
        let (v, cfg) = marks_for_value mdecl infos {env with v=v'} uvar v
        (v, List.fold (remove_var_marks infos) cfg names)

    ////////////////////////////////////////////////////////////////////////////

    // Some utility functions
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

    let fun_marks_matching infos m str ovs : FunMarks =
        let value_match v dv =
            match dv with
            | None -> true
            | Some dv -> AST.value_equal infos v dv
        let match_pattern fm =
            match fm with
            | (s, _) when s<>str -> false
            | (_, lst) -> List.forall2 value_match lst ovs
        (Set.filter match_pattern m.f)

    // Used in the fun assign case
    let compute_neighbors_with_perm infos cfg marked str vs transform inv_trans permut =
        let (m,um,_) = cfg
        let f = Helper.permutation_to_fun permut
        let inv_f = Helper.permutation_to_fun (Helper.inv_permutation permut)
        let n = List.length vs
        let vs = List.permute f vs
        // acc: i, constraints, neighbors list, universally quantified neighbors list
        let aux (i, prev_constraints, nlist, unlist) v =
            let real_i = inv_f i
            let neighbors_m = fun_marks_matching infos m str (transform prev_constraints)
            let neighbors_m = Set.map (fun (_, l) -> List.item real_i (inv_trans l)) neighbors_m
            let neighbors_m = Set.remove v neighbors_m
            let neighbors_um = fun_marks_matching infos um str (transform prev_constraints)
            let neighbors_um = Set.map (fun (_, l) -> List.item real_i (inv_trans l)) neighbors_um
            let neighbors_um = Set.remove v neighbors_um
            let marked = marked || not (Set.isEmpty neighbors_m && Set.isEmpty neighbors_um)

            let constr = if marked then Some v else None
            let new_constraints = Helper.list_set real_i constr prev_constraints
            let new_nlist = Helper.list_set real_i neighbors_m nlist
            let new_unlist = Helper.list_set real_i neighbors_um unlist
            (i+1, new_constraints, new_nlist, new_unlist)
        let empty_lst = List.init n (fun _ -> Set.empty)
        let (_,cs,ns,uns) = List.fold aux (0, List.init n (fun _ -> None), empty_lst, empty_lst) vs
        (List.map (fun c -> c <> None) cs, ns, uns)

    let add_ineq_between infos m cvs1 cvs2 =
        let aux m cv =
            Set.fold (fun m cv' -> add_diff_constraint infos m cv cv') m cvs1
        Set.fold aux m cvs2

    ////////////////////////////////////////////////////////////////////////////

    let rec marks_before_statement mdecl infos tr cfg =
        match tr with
        | TrNewBlock (_, decls, tr_sts) ->
            let cfg' = config_enter_block infos cfg decls
            let cfg' = marks_before_statements mdecl infos tr_sts cfg'
            config_leave_block infos cfg' decls cfg
        | TrVarAssign ((env,_,_), str, v) ->
            let marked = is_var_marked infos cfg str
            let cfg = remove_var_marks infos cfg str
            if marked
            then
                let (_,cfg') = marks_for_value mdecl infos env Set.empty v
                config_union cfg cfg'
            else cfg
        | TrVarAssignAction ((env,_,b), _, str, input, output, args, tr) ->
            let (marked, cfg) =
                if b then
                    (is_var_marked infos cfg str, remove_var_marks infos cfg str)
                else (false, cfg)

            let cfg' = config_enter_block infos cfg (output::input)
            let cfg' =
                let (m, um, ad) = cfg'
                if marked then
                    ({ m with v = Set.add output.Name m.v }, um, ad)
                else (m, um, ad)

            let cfg' = marks_before_statement mdecl infos tr cfg'
            let args_marks = List.map (is_var_marked infos cfg') (List.map (fun (decl:VarDecl) -> decl.Name) input)
            let cfg = config_leave_block infos cfg' (output::input) cfg
            
            let args = List.zip args args_marks
            let (args, _) = List.unzip (List.filter (fun (_,marked) -> marked) args)
            let (_, args_cfg) = List.unzip (List.map (marks_for_value mdecl infos env Set.empty) args)
            config_union_many (cfg::args_cfg)
        | TrFunAssign ((env,_,_), str, hvs, v) ->
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
            let (vs, uvs) = Interpreter.separate_hvals hvs
            let cvs = List.map (Interpreter.evaluate_value mdecl infos env) vs
            let some_cvs = List.map (fun a -> Some a) cvs
            let none_uvs = List.map (fun _ -> None) uvs
            let constraints = Interpreter.reconstruct_hvals hvs some_cvs none_uvs
            let (m,um,_) = cfg
            let m_marks = fun_marks_matching infos m str constraints
            let um_marks = fun_marks_matching infos um str constraints
            let all_marks = Set.union m_marks um_marks

            let marked = not (Set.isEmpty all_marks)
            let cfg = Set.fold (fun cfg (_,vs) -> remove_fun_marks infos cfg str vs) cfg all_marks

            // Adding marks for the important values of v
            let compute_marks_for (env:Model.Environment) v uvs model_dependent uvs_inst =
                let uvars =
                    if model_dependent
                    then
                        let md_uvs = Set.filter (fun (d:VarDecl) -> is_model_dependent_type d.Type) (Set.ofList uvs)
                        Set.map (fun (d:VarDecl) -> d.Name) md_uvs
                    else Set.empty
                marks_for_value_with mdecl infos env uvars v (List.map (fun (d:VarDecl) -> d.Name) uvs) uvs_inst
            let add_marks_for_all (env:Model.Environment) v uvs model_dependent uvs_insts cfg =
                let aux acc uvs_inst =
                    let (_,cfg) = compute_marks_for env v uvs model_dependent uvs_inst
                    config_union acc cfg
                Set.fold aux cfg uvs_insts

            let m_marks = Set.map (fun (_,cvs) -> Interpreter.keep_only_holes hvs cvs) m_marks
            let cfg = add_marks_for_all env v uvs false m_marks cfg
            let um_marks = Set.map (fun (_,cvs) -> Interpreter.keep_only_holes hvs cvs) um_marks
            let cfg = add_marks_for_all env v uvs true um_marks cfg

            // Adding marks for the important args (vs)
            let permutations = Helper.all_permutations (List.length cvs)
            let transform cvs_opt =
                Interpreter.reconstruct_hvals hvs cvs_opt none_uvs
            let inv_trans = Interpreter.keep_only_vals hvs
            let vals_possibilities = Seq.map (compute_neighbors_with_perm infos cfg marked str cvs transform inv_trans) permutations

            let treat_possibility (vs_marks, neighbors, uneighbors) =
                let args = List.zip vs vs_marks
                let (args, _) = List.unzip (List.filter (fun (_,marked) -> marked) args)
                let (_, args_cfg) = List.unzip (List.map (marks_for_value mdecl infos env Set.empty) args)
                let cfg = config_union_many (cfg::args_cfg)
                // Disequality marks
                let (m, um, ad) = cfg
                let m = Seq.fold2 (fun m cv ns -> add_ineq_between infos m (Set.singleton cv) ns) m cvs neighbors
                let um = Seq.fold2 (fun um cv ns -> add_ineq_between infos um (Set.singleton cv) ns) um cvs uneighbors
                (m,um,ad)

            let results = Seq.map treat_possibility vals_possibilities
            Helper.seq_min is_better_config results
        | TrIfElse ((env,_,_), v, tr) ->
            let cfg = marks_before_statement mdecl infos tr cfg
            let (_,cfg') = marks_for_value mdecl infos env Set.empty v
            config_union cfg cfg'
        | TrIfSomeElse ((env,_,_), cv, decl, v, tr) ->
            match cv with
            | Some _ ->
                let cfg' = config_enter_block infos cfg [decl]
                let cfg' = marks_before_statement mdecl infos tr cfg'
                let (_, cfg'') =
                    if is_var_marked infos cfg' decl.Name
                    then marks_for_value mdecl infos (initial_env tr) Set.empty v
                    (* NOTE: In the case above, we may also ensure that every other value doesn't satisfy the predicate.
                       However, it is a different problem than garanteeing the invariant value,
                       since we are bound to an execution (maybe there is no uniqueness in this execution).
                       Therefore, we suppose that the choice made is always the value we choose here (if it satisfies the condition).
                       An assertion can also be added by the user to ensure this uniqueness. *)
                    else marks_for_value mdecl infos env Set.empty (ValueNot (ValueForall (decl, ValueNot v)))
                let cfg' = config_union cfg' cfg''
                config_leave_block infos cfg' [decl] cfg
            | None ->
                let cfg = marks_before_statement mdecl infos tr cfg
                let (_,cfg') = marks_for_value mdecl infos env Set.empty (ValueForall (decl, ValueNot v))
                config_union cfg cfg'
        | TrAssert ((env,_,_),v) ->
            let (_, cfg') = marks_for_value mdecl infos env Set.empty v
            config_union cfg cfg'

    // Statements are analysed in reverse order
    and marks_before_statements mdecl infos trs cfg =
        let aux cfg tr =
            marks_before_statement mdecl infos tr cfg
        List.fold aux cfg (List.rev trs)


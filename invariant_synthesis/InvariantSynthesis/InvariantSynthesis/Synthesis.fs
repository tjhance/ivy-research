module Synthesis

    open MinimalAST
    open Trace
    open Interpreter

    type FunMarks = Set<string * List<ConstValue>>
    type VarMarks = Set<string>
    type DiffConstraint = Set<ConstValue * ConstValue> // We don't impose disequality if is not necessary

    type Marks = { f : FunMarks; v : VarMarks; d: DiffConstraint }

    // Indicate for each umark which arguments are potentially model-dependent
    type UniversalFunMarksInfo = Map<string * List<ConstValue>,Set<int>>
    type AdditionalData = { md : bool ; ufmi : UniversalFunMarksInfo } // md means model-dependent

    let empty_marks = { f = Set.empty; v = Set.empty ; d = Set.empty }
    let empty_ad = { md = false ; ufmi = Map.empty }
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

    let ad_reduce op1 op2 ads : AdditionalData =
        let mds = Seq.map (fun ad -> ad.md) ads
        let ufmis = Seq.map (fun ad -> ad.ufmi) ads
        { md = op1 mds ; ufmi = op2 ufmis }
    
    let marks_union_many = marks_reduce Set.unionMany Set.unionMany Set.unionMany
    let marks_union m1 m2 = marks_union_many ([m1;m2] |> List.toSeq)
    let marks_diff m1 m2 =
        { f=Set.difference m1.f m2.f ; v=Set.difference m1.v m2.v; d=Set.difference m1.d m2.d }

    let ad_union_many =
        let union_ufmis ufmis =
            let aux acc ufmi =
                let merge_key acc k v =
                    let s =
                        match Map.tryFind k acc with
                        | None -> v
                        | Some s -> Set.union s v
                    Map.add k s acc
                Map.fold merge_key acc ufmi
            Seq.fold aux Map.empty ufmis
        ad_reduce (Seq.exists Helper.identity) union_ufmis
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

    let add_diff_constraint m cv1 cv2 =
        let d' = Set.add (cv1, cv2) m.d
        let d' = Set.add (cv2, cv1) d'
        { m with d=d' }

    let get_ufmi_entry (ad:AdditionalData) str cvs =
         match Map.tryFind (str, cvs) ad.ufmi with
         | None -> Set.empty
         | Some s -> s

    let add_ufmi_entry (ad:AdditionalData) str cvs arg =
        let s = get_ufmi_entry ad str cvs
        let s = Set.add arg s
        { ad with ufmi = Map.add (str, cvs) s ad.ufmi }

    let remove_ufmi_entry (ad:AdditionalData) str cvs =
        { ad with ufmi = Map.remove (str, cvs) ad.ufmi }

    let is_var_marked (m, um, _) var =
        (Set.contains var m.v) || (Set.contains var um.v)
    
    let remove_var_marks (m, um, ad) var : Marks * Marks * AdditionalData =
        ({m with v = Set.remove var m.v}, {um with v = Set.remove var um.v}, ad)

    let config_is_included (m1,um1,ad1) (m2,um2,ad2) =
        let ad_is_included (ad1:AdditionalData) (ad2:AdditionalData) =
            if ad1.md && not ad2.md
            then false
            else
                let is_included (str, cvs) is =
                    match Map.tryFind (str, cvs) ad2.ufmi with
                    | None -> Set.isEmpty is
                    | Some is' -> Set.isSubset is is' 
                Map.forall is_included ad1.ufmi
        let marks_are_included m1 m2 =
            Set.isSubset m1.f m2.f && Set.isSubset m1.v m2.v
        ad_is_included ad1 ad2 && marks_are_included m1 m2 && marks_are_included um1 um2

    let remove_worst_configs cfgs =
        let is_strictly_included cfg1 cfg2 =
            cfg1 <> cfg2 && config_is_included cfg1 cfg2
        let remove_worse acc cfg =
            Set.filter (fun cfg' -> not (is_strictly_included cfg cfg')) acc
        Set.fold remove_worse cfgs cfgs

    exception InvalidOperation
    let bool_of_cv cv =
        match cv with
        | AST.ConstBool b -> b
        | _ -> raise TypeError

    // uvar: variables that can browse an arbitrary large range (depending on the model)
    let rec marks_for_value mdecl infos env uvar v : ConstValue * Set<Marks * Marks * AdditionalData> =
        let (v, cfgs) =
            match v with
            | ValueConst c -> (c, Set.singleton empty_config)
            | ValueStar t -> (AST.type_default_value t, Set.singleton empty_config)
            | ValueVar str ->
                let eval = evaluate_value mdecl infos env (ValueVar str)
                if Set.contains str uvar
                then (eval, Set.singleton (empty_marks, { empty_marks with v=Set.singleton str }, { empty_ad with md=true }))
                else (eval, Set.singleton ({ empty_marks with v=Set.singleton str }, empty_marks, empty_ad))
            | ValueFun (str, values) ->
                let res = List.map (marks_for_value mdecl infos env uvar) values
                let (cvs, cfgs) = List.unzip res
                let vs = List.map (fun cv -> ValueConst cv) cvs
                let eval = evaluate_value mdecl infos env (ValueFun (str, vs))
                let cfgs = Helper.all_choices_combination cfgs
                let treat_cfgs cfgs =
                    let (m,um,ad) = config_union_many cfgs
                    if ad.md
                    then
                        let add_entry_if_needed (i, acc) (_,_,ad:AdditionalData) =
                            if ad.md
                            then (i+1, add_ufmi_entry acc str cvs i)
                            else (i+1, acc)
                        let (_,ad) = List.fold add_entry_if_needed (0, ad) cfgs
                        (m, { um with f = Set.add (str, cvs) um.f }, ad)
                    else
                        ({ m with f = Set.add (str, cvs) m.f }, um, ad)
                (eval, Set.ofSeq (Seq.map treat_cfgs cfgs))
            | ValueEqual (v1, v2) ->
                let (cv1, cfgs1) = marks_for_value mdecl infos env uvar v1
                let (cv2, cfgs2) = marks_for_value mdecl infos env uvar v2
                let cfgs = Helper.all_choices_combination [cfgs1;cfgs2]
                let eval = AST.value_equal cv1 cv2
                let treat_cfg cfg =
                    let (cfg1, cfg2) = Helper.lst_to_couple cfg
                    let (m,um,ad) = config_union cfg1 cfg2
                    if eval then (m, um, ad)
                    else if ad.md
                    then (m, add_diff_constraint um cv1 cv2, ad)
                    else (add_diff_constraint m cv1 cv2, um, ad)
                (AST.ConstBool eval, Set.ofSeq (Seq.map treat_cfg cfgs))
            | ValueOr (v1, v2) ->
                let (cv1, cfgs1) = marks_for_value mdecl infos env uvar v1
                let (cv2, cfgs2) = marks_for_value mdecl infos env uvar v2
                let cfgs = Helper.all_choices_combination [cfgs1;cfgs2]
                let eval = (bool_of_cv cv1) || (bool_of_cv cv2)
                let treat_cfg cfg =
                    let (cfg1, cfg2) = Helper.lst_to_couple cfg
                    match cv1, cv2 with
                    | AST.ConstBool false, AST.ConstBool false -> [config_union cfg1 cfg2]
                    | AST.ConstBool true, AST.ConstBool false -> [cfg1]
                    | AST.ConstBool false, AST.ConstBool true -> [cfg2]
                    | AST.ConstBool true, AST.ConstBool true -> [cfg1 ; cfg2]
                    | _, _ -> raise TypeError
                (AST.ConstBool eval, Set.ofSeq (Seq.concat (Seq.map treat_cfg cfgs)))
            | ValueNot v ->
                let (cv,cfgs) = marks_for_value mdecl infos env uvar v
                (value_not cv, cfgs)
            | ValueSomeElse (d,f,v) ->
                match if_some_value mdecl infos env d f with
                | Some cv ->
                    (* NOTE: See note for IfSomeElse statement. *)
                    let is_uvar = is_model_dependent_type d.Type && not (Set.isEmpty uvar) 
                    let uvar = if is_uvar then Set.add d.Name uvar else uvar
                    let (_,cfgs) = marks_for_value_with mdecl infos env uvar f [d.Name] [cv]
                    (cv,cfgs)
                | None -> 
                    let (_,cfgs1) = marks_for_value mdecl infos env uvar (ValueForall (d, ValueNot f))
                    let (cv,cfgs2) = marks_for_value mdecl infos env uvar v
                    let cfgs = Helper.all_choices_combination [cfgs1;cfgs2]
                    (cv, Set.ofSeq (Seq.map config_union_many cfgs))
            | ValueIfElse (f, v1, v2) ->
                let (b, cfgs) = marks_for_value mdecl infos env uvar f
                let (res, cfgs') =
                    match b with
                    | AST.ConstBool true -> marks_for_value mdecl infos env uvar v1
                    | AST.ConstBool false -> marks_for_value mdecl infos env uvar v2
                    | _ -> raise TypeError
                let cfgs = Helper.all_choices_combination [cfgs;cfgs']
                (res, Set.ofSeq (Seq.map config_union_many cfgs))
            | ValueForall (decl, v) ->
                let is_uvar = 
                    is_model_dependent_type decl.Type && 
                    (not (Set.isEmpty uvar) || evaluate_value mdecl infos env (ValueForall (decl, v)) = AST.ConstBool true)
                let uvar = if is_uvar then Set.add decl.Name uvar else uvar
                let values = List.ofSeq (Model.all_values infos decl.Type)
                let all_possibilities = List.map (fun cv -> marks_for_value_with mdecl infos env uvar v [decl.Name] [cv]) values
                if Seq.forall (fun (b,_) -> b = AST.ConstBool true) all_possibilities
                then
                    // We mix all contraints (some will probably be model-dependent)
                    let cfgs = Helper.all_choices_combination (List.map (fun (_,cfgs) -> cfgs) all_possibilities)
                    (AST.ConstBool true, Set.ofSeq (Seq.map config_union_many cfgs))
                else
                    // We pick one constraint that breaks the forall
                    let possibilities = Seq.filter (fun (b, _) -> b = AST.ConstBool false) all_possibilities
                    let possibilities = Seq.concat (Seq.map (fun (_,cfgs) -> cfgs) possibilities)
                    (AST.ConstBool false, Set.ofSeq possibilities)
            | ValueInterpreted (str, vs) ->
                let res = List.map (marks_for_value mdecl infos env uvar) vs
                let (cvs, cfgs) = List.unzip res
                let cfgs = Helper.all_choices_combination cfgs
                let eval = (find_interpreted_action mdecl str).Effect infos env cvs
                (eval, Set.ofSeq (Seq.map config_union_many cfgs))
        (v, remove_worst_configs cfgs)

    and marks_for_value_with mdecl infos (env:Model.Environment) uvar v names values =
        let v' = List.fold2 (fun acc n v -> Map.add n v acc) env.v names values
        let (v, cfgs) = marks_for_value mdecl infos {env with v=v'} uvar v
        (v, Set.map (fun cfg -> List.fold remove_var_marks cfg names) cfgs)

    let union_of_cfg_possibilities cfgs =
        let cfgs = Helper.all_choices_combination cfgs
        let cfgs = Set.ofSeq (Seq.map config_union_many cfgs)
        remove_worst_configs cfgs

    let best_cfg cfgs =
        Helper.seq_min is_better_config cfgs

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
    
    let remove_fun_marks _ (m, um, ad) str cvs : Marks * Marks * AdditionalData =
        ({m with f = Set.remove (str,cvs) m.f},
            {um with f = Set.remove (str,cvs) um.f},
            remove_ufmi_entry ad str cvs)

    let fun_marks_matching_ext (m, um, ad) str ovs md_predicate : (FunMarks * FunMarks) =
        let aux m =
            let value_match v dv =
                match dv with
                | None -> true
                | Some dv -> AST.value_equal v dv
            let match_pattern model_dep fm =
                match fm with
                | (s, _) when s<>str -> false
                | (_, lst) ->
                    if List.forall2 value_match lst ovs
                    then
                        let ufmi = get_ufmi_entry ad str lst
                        if model_dep
                        then md_predicate ufmi
                        else not (md_predicate ufmi)
                    else false
            let matches = (Set.filter (match_pattern false) m.f)
            let matches' = (Set.filter (match_pattern true) m.f)
            (matches, matches')
        let (matches, matches') = aux m
        let (matches'', umatches) = aux um
        (Set.unionMany [matches; matches'; matches''], umatches)

    let fun_marks_matching cfg str ovs : (FunMarks * FunMarks) =
        let md_pred ufmi =
            Helper.existsi (fun i ov -> ov = None && Set.contains i ufmi) ovs
        fun_marks_matching_ext cfg str ovs md_pred

    // Used in the fun assign case
    let compute_neighbors_with_perm cfg marked str vs hvs none_uvs permut =

        let transform cvs_opt = reconstruct_hvals hvs cvs_opt none_uvs
        let inv_trans1 = keep_only_vals hvs
        let inv_trans2 = keep_only_vals hvs

        let f = Helper.permutation_to_fun permut
        let inv_f = Helper.permutation_to_fun (Helper.inv_permutation permut)
        let n = List.length vs
        let vs = List.permute f vs
        // acc: i, constraints, neighbors list, universally quantified neighbors list
        let aux (i, prev_constraints, nlist, unlist) v =
            let real_i = inv_f i

            let full_constraints = transform prev_constraints

            let md_pred ufmi =
                let ufmi_lst = List.init (List.length full_constraints) (fun i -> Set.contains i ufmi)
                List.item real_i (inv_trans1 ufmi_lst)
                
            let (neighbors_m, neighbors_um) = fun_marks_matching_ext cfg str full_constraints md_pred
            let neighbors_m = Set.map (fun (_, l) -> List.item real_i (inv_trans2 l)) neighbors_m
            let neighbors_m = Set.remove v neighbors_m
            let neighbors_um = Set.map (fun (_, l) -> List.item real_i (inv_trans2 l)) neighbors_um
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

    let add_ineq_between m cvs1 cvs2 =
        let aux m cv =
            Set.fold (fun m cv' -> add_diff_constraint m cv cv') m cvs1
        Set.fold aux m cvs2

    ////////////////////////////////////////////////////////////////////////////

    let rec marks_before_statement mdecl infos ignore_asserts ignore_assumes tr cfg =
        let rec aux group_trs cfg =
            if List.isEmpty group_trs then cfg
            else
                let tr = List.head group_trs
                let group_trs = List.tail group_trs
                match tr with
                | TrAtomicGroup (_, trs) ->
                    let cfg = aux (List.rev trs) cfg
                    aux group_trs cfg
                | TrNewBlock (_, decls, trs) ->
                    let cfg' = config_enter_block infos cfg decls
                    let cfg' = marks_before_statements mdecl infos ignore_asserts ignore_assumes trs cfg'
                    aux group_trs (config_leave_block infos cfg' decls cfg)
                | TrVarAssign ((env,_,_), str, v) ->
                    let marked = is_var_marked cfg str
                    let cfg = remove_var_marks cfg str
                    let cfgs =
                        if marked
                        then
                            let (_,cfgs) = marks_for_value mdecl infos env Set.empty v
                            union_of_cfg_possibilities [Set.singleton cfg;cfgs]
                        else Set.singleton cfg
                    let cfgs = Set.map (fun cfg -> aux group_trs cfg) cfgs
                    best_cfg cfgs
                | TrVarAssignAction ((env,_,b), str, input, output, args, tr) ->
                    let (marked, cfg) =
                        if b then
                            (is_var_marked cfg str, remove_var_marks cfg str)
                        else (false, cfg)

                    let cfg' = config_enter_block infos cfg (output::input)
                    let cfg' =
                        let (m, um, ad) = cfg'
                        if marked then
                            ({ m with v = Set.add output.Name m.v }, um, ad)
                        else (m, um, ad)

                    let cfg' = marks_before_statement mdecl infos ignore_asserts ignore_assumes tr cfg'
                    let args_marks = List.map (is_var_marked cfg') (List.map (fun (decl:VarDecl) -> decl.Name) input)
                    let cfg = config_leave_block infos cfg' (output::input) cfg
            
                    let args = List.zip args args_marks
                    let (args, _) = List.unzip (List.filter (fun (_,marked) -> marked) args)
                    let (_, args_cfgs) = List.unzip (List.map (marks_for_value mdecl infos env Set.empty) args)
                    let cfgs = union_of_cfg_possibilities ((Set.singleton cfg)::args_cfgs)
                    let cfgs = Set.map (fun cfg -> aux group_trs cfg) cfgs
                    best_cfg cfgs
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
                    let (vs, uvs) = separate_hvals hvs
                    let cvs = List.map (Interpreter.evaluate_value mdecl infos env) vs
                    let some_cvs = List.map (fun a -> Some a) cvs
                    let none_uvs = List.map (fun _ -> None) uvs
                    let constraints = reconstruct_hvals hvs some_cvs none_uvs
                    let (m_marks,um_marks) = fun_marks_matching cfg str constraints
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
                    let add_marks_for_all (env:Model.Environment) v uvs model_dependent uvs_insts cfgs =
                        let aux acc uvs_inst =
                            let (_,cfgs) = compute_marks_for env v uvs model_dependent uvs_inst
                            union_of_cfg_possibilities [acc; cfgs]
                        Set.fold aux cfgs uvs_insts

                    let m_marks = Set.map (fun (_,cvs) -> keep_only_holes hvs cvs) m_marks
                    let cfgs = add_marks_for_all env v uvs false m_marks (Set.singleton cfg)
                    let um_marks = Set.map (fun (_,cvs) -> keep_only_holes hvs cvs) um_marks
                    let cfgs = add_marks_for_all env v uvs true um_marks cfgs

                    let treat_cfg cfg =
                        // Adding marks for the important args (vs)
                        let permutations = List.ofSeq (Helper.all_permutations (List.length cvs))
                        let vals_possibilities = List.map (compute_neighbors_with_perm cfg marked str cvs hvs none_uvs) permutations

                        let treat_possibility (vs_marks, neighbors, uneighbors) =
                            let args = List.zip vs vs_marks
                            let (args, _) = List.unzip (List.filter (fun (_,marked) -> marked) args)
                            let (_, args_cfgs) = List.unzip (List.map (marks_for_value mdecl infos env Set.empty) args)
                            let cfgs = union_of_cfg_possibilities ((Set.singleton cfg)::args_cfgs)
                            // Disequality marks
                            let treat_cfg cfg =
                                let (m, um, ad) = cfg
                                let m = Seq.fold2 (fun m cv ns -> add_ineq_between m (Set.singleton cv) ns) m cvs neighbors
                                let um = Seq.fold2 (fun um cv ns -> add_ineq_between um (Set.singleton cv) ns) um cvs uneighbors
                                aux group_trs (m,um,ad)
                            let cfgs = Set.map treat_cfg cfgs
                            best_cfg cfgs

                        let results = List.map treat_possibility vals_possibilities
                        best_cfg results
                    let cfgs = Set.map treat_cfg cfgs
                    best_cfg cfgs
                | TrIfElse ((env,_,_), v, tr) ->
                    let cfg = marks_before_statement mdecl infos ignore_asserts ignore_assumes tr cfg
                    let (_,cfgs) = marks_for_value mdecl infos env Set.empty v
                    let cfgs = union_of_cfg_possibilities [Set.singleton cfg;cfgs]
                    let cfgs = Set.map (fun cfg -> aux group_trs cfg) cfgs
                    best_cfg cfgs
                | TrIfSomeElse ((env,_,_), cv, decl, v, tr) ->
                    match cv with
                    | Some _ ->
                        let cfg' = config_enter_block infos cfg [decl]
                        let cfg' = marks_before_statement mdecl infos ignore_asserts ignore_assumes tr cfg'
                        let (_, cfgs) =
                            if is_var_marked cfg' decl.Name
                            then marks_for_value mdecl infos (initial_env tr) Set.empty v
                            (* NOTE: In the case above, we may also ensure that every other value doesn't satisfy the predicate.
                               However, it is a different problem than garanteeing the invariant value,
                               since we are bound to an execution (maybe there is no uniqueness in this execution).
                               Therefore, we suppose that the choice made is always the value we choose here (if it satisfies the condition).
                               An assertion can also be added by the user to ensure this uniqueness. *)
                            else marks_for_value mdecl infos env Set.empty (ValueNot (ValueForall (decl, ValueNot v)))
                        let cfgs = union_of_cfg_possibilities [Set.singleton cfg';cfgs]
                        let cfgs = Set.map (fun cfg' -> aux group_trs (config_leave_block infos cfg' [decl] cfg)) cfgs
                        best_cfg cfgs
                    | None ->
                        let cfg = marks_before_statement mdecl infos ignore_asserts ignore_assumes tr cfg
                        let (_,cfgs) = marks_for_value mdecl infos env Set.empty (ValueForall (decl, ValueNot v))
                        let cfgs = union_of_cfg_possibilities [Set.singleton cfg;cfgs]
                        let cfgs = Set.map (fun cfg -> aux group_trs cfg) cfgs
                        best_cfg cfgs
                | TrAssert ((env,_,b),v) ->
                    // If ignore_asserts is true, we ignore satisfied assertions
                    if ignore_asserts && b then
                        aux group_trs cfg
                    else
                        let (_, cfgs) = marks_for_value mdecl infos env Set.empty v
                        let cfgs = union_of_cfg_possibilities [Set.singleton cfg;cfgs]
                        let cfgs = Set.map (fun cfg -> aux group_trs cfg) cfgs
                        best_cfg cfgs
                | TrAssume ((env,_,b),v) ->
                    // If ignore_assumes is true, we ignore satisfied assumptions
                    if ignore_assumes && b then
                        aux group_trs cfg
                    else
                        let (_, cfgs) = marks_for_value mdecl infos env Set.empty v
                        let cfgs = union_of_cfg_possibilities [Set.singleton cfg;cfgs]
                        let cfgs = Set.map (fun cfg -> aux group_trs cfg) cfgs
                        best_cfg cfgs
        aux [tr] cfg

    // Statements are analysed in reverse order
    and marks_before_statements mdecl infos ignore_asserts ignore_assumes trs cfg =
        let aux cfg tr =
            marks_before_statement mdecl infos ignore_asserts ignore_assumes tr cfg
        List.fold aux cfg (List.rev trs)


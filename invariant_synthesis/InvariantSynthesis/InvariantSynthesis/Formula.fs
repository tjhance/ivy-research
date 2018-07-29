module Formula

    open AST

    let binary_relation_implication rel1 value1 rel2 value2 =
        let l = [FunPattern (PatternConst value1, rel1, [PatternVar "X"; PatternVar "Y"])] |> Set.ofList
        let r = [FunPattern (PatternConst value2, rel2, [PatternVar "X"; PatternVar "Y"])] |> Set.ofList
        let i1 = (l,r)
        let l = [FunPattern (PatternConst (not value2), rel2, [PatternVar "X"; PatternVar "Y"])] |> Set.ofList
        let r = [FunPattern (PatternConst (not value1), rel1, [PatternVar "X"; PatternVar "Y"])] |> Set.ofList
        let i2 = (l,r)
        [i1;i2]

    let reflexive relname relvalue typename =
        let l = Set.empty
        let r = [FunPattern (PatternConst relvalue, relname, [PatternVar "X"; PatternVar "X"])] |> Set.ofList
        let i1 = (l,r)
        let l = [FunPattern (PatternConst (not relvalue), relname, [PatternVar "X"; PatternVar "Y"])] |> Set.ofList
        let r = [ValueDiffPattern (Uninterpreted typename, PatternVar "X", PatternVar "Y")] |> Set.ofList
        let i2 = (l,r)
        [i1;i2]
    
    let transitive relname relvalue =
        let l = [FunPattern (PatternConst relvalue, relname, [PatternVar "X"; PatternVar "Y"]) ;
            FunPattern (PatternConst relvalue, relname, [PatternVar "Y"; PatternVar "Z"])] |> Set.ofList
        let r = [FunPattern (PatternConst relvalue, relname, [PatternVar "X"; PatternVar "Z"])] |> Set.ofList
        let i1 = (l,r)
        let l = [FunPattern (PatternConst (not relvalue), relname, [PatternVar "X"; PatternVar "Z"]) ;
            FunPattern (PatternConst relvalue, relname, [PatternVar "X"; PatternVar "Y"])] |> Set.ofList
        let r = [FunPattern (PatternConst (not relvalue), relname, [PatternVar "Y"; PatternVar "Z"])] |> Set.ofList
        let i2 = (l,r)
        let l = [FunPattern (PatternConst (not relvalue), relname, [PatternVar "X"; PatternVar "Z"]) ;
            FunPattern (PatternConst relvalue, relname, [PatternVar "Y"; PatternVar "Z"])] |> Set.ofList
        let r = [FunPattern (PatternConst (not relvalue), relname, [PatternVar "X"; PatternVar "Y"])] |> Set.ofList
        let i3 = (l,r)
        [i1;i2;i3]

    let symetric relname =
        let l = [FunPattern (PatternConst true, relname, [PatternVar "X"; PatternVar "Y"])] |> Set.ofList
        let r = [FunPattern (PatternConst true, relname, [PatternVar "Y"; PatternVar "X"])] |> Set.ofList
        let i1 = (l,r)
        let l = [FunPattern (PatternConst false, relname, [PatternVar "X"; PatternVar "Y"])] |> Set.ofList
        let r = [FunPattern (PatternConst false, relname, [PatternVar "Y"; PatternVar "X"])] |> Set.ofList
        let i2 = (l,r)
        [i1;i2]

    let antisymetric relname relvalue typename =
        let l = [FunPattern (PatternConst relvalue, relname, [PatternVar "X"; PatternVar "Y"]) ;
            ValueDiffPattern (Uninterpreted typename, PatternVar "X", PatternVar "Y")] |> Set.ofList
        let r = [FunPattern (PatternConst (not relvalue), relname, [PatternVar "Y"; PatternVar "X"])] |> Set.ofList
        let i1 = (l,r)
        [i1]

    exception DoesntMatch
    exception EndCondition

    let all_diffs_for_type types infos t =
        if Marking.is_model_dependent_type t then Set.empty
        else
            let couples = Model.all_values_ext types infos [t;t]
            let couples = Seq.map Helper.lst_to_couple couples
            let couples = Seq.filter (fun (a,b) -> not (value_equal a b)) couples
            Set.ofSeq couples

    // Note: this function is not used anymore (Z3 is used instead)
    let simplify_marks types infos (impls:List<AST.ImplicationRule>) (decls:Model.Declarations) (env:Model.Environment) (m:Marking.Marks) =

        let value_equal cv1 cv2 = AST.value_equal cv1 cv2

        let value_diff diffs cv1 cv2 =
            if Marking.is_model_dependent_value cv1 && Marking.is_model_dependent_value cv2
            then Set.contains (cv1,cv2) diffs || Set.contains (cv2,cv1) diffs
            else not (value_equal cv1 cv2)

        let add_diff_constraint diffs cv1 cv2 =
            Set.add (cv2,cv1) (Set.add (cv1,cv2) diffs)

        let remove_diff_constraint diffs cv1 cv2 =
            Set.remove (cv2,cv1) (Set.remove (cv1,cv2) diffs)

        let free_vars_of_pattern p =
            let aux acc t v =
                match v with
                | PatternVar name ->
                    Set.add (AST.default_var_decl name t) acc
                | PatternConst _ -> acc
            match p with
            | FunPattern (_, str, vs) ->
                let types = (Map.find str decls.f).Input
                List.fold2 aux Set.empty types vs
            | ValueDiffPattern (t,n1,n2) ->
                List.fold2 aux Set.empty [t;t] [n1;n2]
        
        let free_vars_of_patterns ps =
            Set.fold (fun acc p -> Set.union acc (free_vars_of_pattern p)) Set.empty ps

        let update_dico dico patval cv =
            match patval with
            | PatternConst b ->
                if value_equal cv (ConstBool b) then dico
                else raise DoesntMatch
            | PatternVar str ->
                if Map.containsKey str dico
                then
                    if value_equal (Map.find str dico) cv then dico
                    else raise DoesntMatch
                else Map.add str cv dico

        let all_dicos_matching_pattern (diffs,mf) p prev_dico =
            match p with
            | FunPattern (pv, str, pvs) ->
                let aux acc (relname,relvalues) =
                    if relname <> str then acc
                    else
                        try
                            let dico = update_dico prev_dico pv (Map.find (relname,relvalues) env.f)
                            Set.add (List.fold2 update_dico dico pvs relvalues) acc
                        with :? DoesntMatch -> acc
                Set.fold aux Set.empty mf
            | ValueDiffPattern (t, pv1, pv2) ->
                let aux acc (cv1,cv2) =
                    if t <> type_of_const_value cv1 || t <> type_of_const_value cv2 then acc
                    else
                        try
                            let dico = update_dico prev_dico pv1 cv1
                            Set.add (update_dico dico pv2 cv2) acc
                        with :? DoesntMatch -> acc
                // We add disequalities for non model-dependent types
                let nmd_diffs = all_diffs_for_type types infos Bool
                let nmd_diffs = Set.unionMany (nmd_diffs::(List.map (all_diffs_for_type types infos) (AST.all_enumerated_types types)))
                Set.fold aux Set.empty (Set.union diffs nmd_diffs)

        let all_dicos_matching_free_var vars prev_dico =
            let is_free_var (d:VarDecl) =
                if Map.containsKey d.Name prev_dico then false
                else true
            let free_vars = Set.toList (Set.filter is_free_var vars)
            let free_types = List.map (fun (v:VarDecl) -> v.Type) free_vars
            let all_values = Model.all_values_ext types infos free_types
            let aux dico free_vars cvs =
                List.fold2 (fun acc (v:VarDecl) cv -> Map.add v.Name cv acc) dico free_vars cvs
            Seq.map (aux prev_dico free_vars) all_values

        let add_constraint dico (diffs,mf) r =
            let resolve pv =
                match pv with
                | PatternConst b -> ConstBool b
                | PatternVar str -> Map.find str dico
            match r with
            | FunPattern (_,str,pvs) ->
                let cvs = List.map resolve pvs
                (diffs,Set.add (str,cvs) mf)
            | ValueDiffPattern (_, pv1, pv2) ->
                let cv1 = resolve pv1
                let cv2 = resolve pv2
                (add_diff_constraint diffs cv1 cv2,mf)

        let add_constraints dico cfg rs =
            Set.fold (add_constraint dico) cfg rs

        let step (diffs, mf) impls
            (already_applied:System.Collections.Generic.Dictionary<Set<Pattern> * Map<string, ConstValue>, unit>) =
            // Apply implication rules one time
            let aux (diffs,mf) (ls,rs) =
                let rec all_dicos ls =
                    match ls with
                    | [] -> Seq.singleton Map.empty
                    | l::ls ->
                        let dicos = all_dicos ls
                        Seq.concat (Seq.map (all_dicos_matching_pattern (diffs,mf) l) dicos)
                let free_vars = free_vars_of_patterns (Set.union ls rs)
                let dicos = all_dicos (Set.toList ls)
                let admfv_if_necessary dico =
                    if already_applied.ContainsKey (rs,dico)
                    then Seq.empty
                    else
                        (
                            already_applied.Add((rs,dico), ())
                            all_dicos_matching_free_var free_vars dico
                        )
                let dicos = Seq.concat (Seq.map admfv_if_necessary dicos)
                Seq.fold (fun acc dico -> add_constraints dico acc rs) (diffs,mf) dicos

            let (diffs,mf) = List.fold aux (diffs,mf) impls
            (diffs, mf)

        let closure diffs mf end_condition =
            // Separate rules
            let impls_base = List.filter (fun (ls, _) -> Set.isEmpty ls) impls
            let impls = List.filter (fun (ls, _) -> not (Set.isEmpty ls)) impls

            // Apply base rules
            let already_applied =
                System.Collections.Generic.Dictionary<Set<Pattern> * Map<string, ConstValue>, unit>()
            let (diffs, mf) = step (diffs, mf) impls_base already_applied

            // Apply other rules until fixpoint
            let step_fp (diffs, mf) =
                let already_applied =
                    System.Collections.Generic.Dictionary<Set<Pattern> * Map<string, ConstValue>, unit>()
                let rec aux (diffs, mf) =
                    let next = step (diffs, mf) impls already_applied
                    if end_condition next then raise EndCondition
                    else if next = (diffs, mf) then next else aux next
                aux (diffs, mf)
            let (diffs, mf) = step_fp (diffs, mf)
            (diffs, mf)

        let mf = m.f
        let diffs = m.d

        // Remove useless relations
        let remove_rel_if_useless acc rel =
            (*let (str,_) = rel
            if (Map.find str decls.f).Output <> Bool // Uncomment if all rules target relations
            then acc
            else*)
                let acc' = Set.remove rel acc
                try
                    ignore (closure diffs acc' (fun (_,cl) -> Set.contains rel cl))
                    acc
                with :? EndCondition -> acc'
        let mf = Set.fold remove_rel_if_useless mf mf

        // Remove useless diff
        let remove_diff_if_useless acc (v1,v2) =
            let acc' = remove_diff_constraint acc v1 v2
            try
                ignore (closure acc' mf (fun (cl,_) -> value_diff cl v1 v2))
                acc
            with :? EndCondition -> acc'
        let diffs = Set.fold remove_diff_if_useless diffs diffs
        
        // Result
        { Marking.v = Set.empty ; Marking.f = mf ; Marking.d = diffs }

    type ValueAssociation =
        | VAConst of ConstValue
        | New of string
        | ExistingVar of string
        | ExistingFun of string * List<ConstValue>

    let formula_for_marks (env:Model.Environment) (mapping:int*Map<ConstValue,ValueAssociation>) (generalize:Set<ConstValue>) (m:Marking.Marks) =

        let var_name nb =
            let c = (char)(65 + nb)
            c.ToString()

        let add_mapping_for_cv (m:Marking.Marks) (next_var,cmap) cv =
            if Marking.is_model_dependent_value cv then
                if Map.containsKey cv cmap then failwith "Concrete value is already mapped!"
                let rec aux_f mfs =
                    match mfs with
                    | [] -> (next_var+1, Map.add cv (New (var_name next_var)) cmap)
                    | (str,cvs)::mfs ->
                        if AST.value_equal (Map.find (str,cvs) env.f) cv
                        then (next_var, Map.add cv (ExistingFun (str,cvs)) cmap)
                        else aux_f mfs
                let rec aux_v mvs =
                    match mvs with
                    | [] -> aux_f (m.f |> Set.toList)
                    | str::mvs ->
                        if AST.value_equal (Map.find str env.v) cv
                        then (next_var, Map.add cv (ExistingVar str) cmap)
                        else aux_v mvs
                aux_v (m.v |> Set.toList)
            else
                (next_var, Map.add cv (VAConst cv) cmap)

        let cv2association (_,mapping) cv =
            try Map.find cv mapping
            with :? System.Collections.Generic.KeyNotFoundException -> VAConst cv

        let rec cv2value (i,mapping) cv =
            let a = cv2association (i,mapping) cv
            match a with
            | VAConst cv -> ValueConst cv
            | New str -> ValueVar str
            | ExistingVar str -> ValueVar str
            | ExistingFun (str, cvs) ->
                let vs = List.map (cv2value (i,mapping)) cvs
                ValueFun (str, vs)

        let all_new_vars (_,mapping) : Set<VarDecl> =
            let content = (Map.toList mapping)
            let content = List.filter (fun (_,assoc) -> match assoc with New _ -> true | _ -> false) content
            let vars =
                List.map
                    (fun (cv,assoc) ->
                        match assoc with
                        | New str -> AST.default_var_decl str (type_of_const_value cv)
                        | _ -> failwith "Invalid association."
                    ) content
            Set.ofList vars

        let replace_new_by_existing (i,mapping) =
            let aux _ a =
                match a with
                | VAConst cv -> VAConst cv
                | New str -> ExistingVar str
                | ExistingVar str -> ExistingVar str
                | ExistingFun (str, cvs) -> ExistingFun (str, cvs)
            let mapping = Map.map aux mapping
            (i, mapping)

        let mapping = Set.fold (fun (i,acc) cv -> (i,Map.remove cv acc)) mapping generalize
        let mapping = Set.fold (add_mapping_for_cv m) mapping generalize

        // We remove trivial equalities
        let v' =
            Set.filter
                (
                    fun str ->
                        let cv = Map.find str env.v
                        cv2association mapping cv <> ExistingVar str
                ) m.v
        let m = {m with v=v'}
        let f' =
            Set.filter
                (
                    fun (str, cvs) ->
                        let cv = Map.find (str, cvs) env.f
                        cv2association mapping cv <> ExistingFun (str, cvs)
                ) m.f
        let m = {m with f=f'}

        // Build constraints
        let constraints_var =
            Set.map
                (
                    fun str ->
                        let cv = Map.find str env.v
                        ValueEqual (ValueVar str, cv2value mapping cv)
                ) m.v
        let constraints_fun =
            Set.map
                (
                    fun (str,cvs) ->
                        let cv = Map.find (str,cvs) env.f
                        let vs = List.map (cv2value mapping) cvs
                        ValueEqual (ValueFun (str, vs), cv2value mapping cv)
                ) m.f
        let constraints = Set.union constraints_var constraints_fun

        // Add inequalities between vars
        let ineq_constraints = // We don't need inequalities when one the values are not model-dependent
                Set.filter (fun (cv1,cv2) -> Marking.is_model_dependent_value cv1 || Marking.is_model_dependent_value cv2) m.d
        let ineq_constraints =
            Set.map
                (
                    fun (cv1,cv2) ->
                        let (cv1,cv2) = Helper.order_tuple (cv1,cv2)
                        let v1 = cv2value mapping cv1
                        let v2 = cv2value mapping cv2
                        ValueNot (ValueEqual (v1, v2))
                ) ineq_constraints
        let constraints = Set.union constraints ineq_constraints

        // Buld formula and list of vars to quantify
        let new_vars = all_new_vars mapping
        let f =
            match constraints |> Set.toList with
            | [] -> ValueConst (ConstBool true)
            | h::constraints -> List.fold (fun acc c -> ValueAnd (acc,c)) h constraints

        // Replace new vars by existing var in the mapping
        let mapping = replace_new_by_existing mapping
        (mapping, new_vars, f)

    let concrete_values_of_marks (env:Model.Environment) (m:Marking.Marks) =
        let add_cvs_var acc str =
            Set.add (Map.find str env.v) acc
        let add_cvs_fun acc (str,cvs) =
            let acc = Set.add (Map.find (str,cvs) env.f) acc
            Set.union acc (Set.ofList cvs)
        let add_cvs_diff acc (cv1, cv2) =
            Set.add cv1 (Set.add cv2 acc)
        let res = Set.fold add_cvs_var Set.empty m.v
        let res = Set.fold add_cvs_fun res m.f
        Set.fold add_cvs_diff res m.d

    let generate_semi_generalized_formula (do_not_generalize:Set<ConstValue>) mapping (env:Model.Environment) (m:Marking.Marks) =
        let all_cvs = concrete_values_of_marks env m
        let generalize = Set.difference all_cvs do_not_generalize
        let (_,new_vars,f) = formula_for_marks env mapping generalize m
        Set.fold (fun acc (d:VarDecl) -> ValueExists (d, acc)) f new_vars

    let generate_semi_generalized_formulas (do_not_generalize:Set<ConstValue>) mapping alt_execs =
        let fs = List.map (fun (m,env) -> generate_semi_generalized_formula do_not_generalize mapping env m) alt_execs
        match fs with
        | [] -> ValueConst (ConstBool false)
        | h::fs -> List.fold (fun acc f -> ValueOr (acc,f)) h fs

    let generate_invariant (env:Model.Environment) (common_cvs:Set<ConstValue>) (m:Marking.Marks) (alt_exec:List<Marking.Marks*Model.Environment>) =
        let generalize = Set.union (concrete_values_of_marks env m) common_cvs
        let (mapping, new_vars, f) = formula_for_marks env (0, Map.empty) generalize m
        let f' = generate_semi_generalized_formulas common_cvs mapping alt_exec

        let f = ValueImply (f,f')
        Set.fold (fun acc (d:VarDecl) -> ValueForall (d, acc)) f new_vars

    let rec simplify_value f =
        match f with
        // Implication
        | ValueImply (f1, ValueConst (ConstBool false)) -> simplify_value (ValueNot f1)
        // Negation
        | ValueNot (ValueEqual (v, ValueConst (ConstBool b)))
        | ValueNot (ValueEqual (ValueConst (ConstBool b), v))
            -> simplify_value (ValueEqual (v, ValueConst (ConstBool (not b))))
        | ValueNot (ValueConst (ConstBool b)) -> simplify_value (ValueConst (ConstBool (not b)))
        | ValueNot (ValueNot f) -> simplify_value f
        //| ValueNot (ValueOr (f1, f2)) -> simplify_value (ValueAnd (ValueNot f1, ValueNot f2))
        //| ValueNot (ValueAnd (f1, f2)) -> simplify_value (ValueOr (ValueNot f1, ValueNot f2))
        | ValueNot (ValueForall (d,f)) -> simplify_value (ValueExists (d, ValueNot f))
        | ValueNot (ValueExists (d,f)) -> simplify_value (ValueForall (d, ValueNot f))
        //| ValueNot (ValueImply (f1, f2)) -> simplify_value (ValueAnd (f1, ValueNot f2))
        // Identity cases
        | ValueConst b -> ValueConst b
        | ValueStar t -> ValueStar t
        | ValueEqual (v1, v2) -> ValueEqual (simplify_value v1, simplify_value v2)
        | ValueOr (f1, f2) -> ValueOr (simplify_value f1, simplify_value f2)
        | ValueAnd (f1, f2) -> ValueAnd (simplify_value f1, simplify_value f2)
        | ValueNot f -> ValueNot (simplify_value f)
        | ValueForall (v, f) -> ValueForall (v, simplify_value f)
        | ValueExists (v, f) -> ValueExists (v, simplify_value f)
        | ValueImply (f1, f2) -> ValueImply (simplify_value f1, simplify_value f2)
        | ValueVar v -> ValueVar v
        | ValueFun (str, vs) -> ValueFun (str, List.map simplify_value vs)
        | ValueMacro (str, vs) -> ValueMacro (str, List.map simplify_value vs)
        | ValueSomeElse (d, v1, v2) -> ValueSomeElse (d, simplify_value v1, simplify_value v2)
        | ValueIfElse (f, v1, v2) -> ValueIfElse (simplify_value f, simplify_value v1, simplify_value v2)
        | ValueInterpreted (str, vs) -> ValueInterpreted (str, List.map simplify_value vs)

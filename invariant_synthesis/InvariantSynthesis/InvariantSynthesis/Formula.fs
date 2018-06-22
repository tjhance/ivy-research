module Formula

    open AST

    let binary_relation_implication rel1 value1 rel2 value2 =
        let l = [RelPattern (PatternConst value1, rel1, [PatternVar "X"; PatternVar "Y"])] |> Set.ofList
        let r = [RelPattern (PatternConst value2, rel2, [PatternVar "X"; PatternVar "Y"])] |> Set.ofList
        let i1 = (l,r)
        let l = [RelPattern (PatternConst (not value2), rel2, [PatternVar "X"; PatternVar "Y"])] |> Set.ofList
        let r = [RelPattern (PatternConst (not value1), rel1, [PatternVar "X"; PatternVar "Y"])] |> Set.ofList
        let i2 = (l,r)
        [i1;i2]

    let reflexive relname relvalue typename =
        let l = Set.empty
        let r = [RelPattern (PatternConst relvalue, relname, [PatternVar "X"; PatternVar "X"])] |> Set.ofList
        let i1 = (l,r)
        let l = [RelPattern (PatternConst (not relvalue), relname, [PatternVar "X"; PatternVar "Y"])] |> Set.ofList
        let r = [ValueDiffPattern (Uninterpreted typename, PatternVar "X", PatternVar "Y")] |> Set.ofList
        let i2 = (l,r)
        [i1;i2]
    
    let transitive relname relvalue =
        let l = [RelPattern (PatternConst relvalue, relname, [PatternVar "X"; PatternVar "Y"]) ;
            RelPattern (PatternConst relvalue, relname, [PatternVar "Y"; PatternVar "Z"])] |> Set.ofList
        let r = [RelPattern (PatternConst relvalue, relname, [PatternVar "X"; PatternVar "Z"])] |> Set.ofList
        let i1 = (l,r)
        let l = [RelPattern (PatternConst (not relvalue), relname, [PatternVar "X"; PatternVar "Z"]) ;
            RelPattern (PatternConst relvalue, relname, [PatternVar "X"; PatternVar "Y"])] |> Set.ofList
        let r = [RelPattern (PatternConst (not relvalue), relname, [PatternVar "Y"; PatternVar "Z"])] |> Set.ofList
        let i2 = (l,r)
        let l = [RelPattern (PatternConst (not relvalue), relname, [PatternVar "X"; PatternVar "Z"]) ;
            RelPattern (PatternConst relvalue, relname, [PatternVar "Y"; PatternVar "Z"])] |> Set.ofList
        let r = [RelPattern (PatternConst (not relvalue), relname, [PatternVar "X"; PatternVar "Y"])] |> Set.ofList
        let i3 = (l,r)
        [i1;i2;i3]

    let symetric relname =
        let l = [RelPattern (PatternConst true, relname, [PatternVar "X"; PatternVar "Y"])] |> Set.ofList
        let r = [RelPattern (PatternConst true, relname, [PatternVar "Y"; PatternVar "X"])] |> Set.ofList
        let i1 = (l,r)
        let l = [RelPattern (PatternConst false, relname, [PatternVar "X"; PatternVar "Y"])] |> Set.ofList
        let r = [RelPattern (PatternConst false, relname, [PatternVar "Y"; PatternVar "X"])] |> Set.ofList
        let i2 = (l,r)
        [i1;i2]

    let antisymetric relname relvalue typename =
        let l = [RelPattern (PatternConst relvalue, relname, [PatternVar "X"; PatternVar "Y"]) ;
            ValueDiffPattern (Uninterpreted typename, PatternVar "X", PatternVar "Y")] |> Set.ofList
        let r = [RelPattern (PatternConst (not relvalue), relname, [PatternVar "Y"; PatternVar "X"])] |> Set.ofList
        let i1 = (l,r)
        [i1]

    exception DoesntMatch
    exception EndCondition

    let simplify_marks infos (impls:List<AST.ImplicationRule>) (decls:Model.Declarations) (env:Model.Environment) (m:Synthesis.Marks) =

        let value_equal cv1 cv2 = AST.value_equal cv1 cv2

        let value_diff diffs cv1 cv2 =
            if Synthesis.is_model_dependent_value cv1 && Synthesis.is_model_dependent_value cv2
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
            | VarPattern _ -> Set.empty
            | RelPattern (_, str, vs) ->
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

        let all_dicos_matching_pattern (diffs,mv,mf) p prev_dico =
            match p with
            | VarPattern (pv,str) ->
                if Set.contains str mv
                then 
                    try
                        let dico = update_dico prev_dico pv (Map.find str env.v)
                        Set.singleton dico
                    with :? DoesntMatch -> Set.empty
                else Set.empty
            | RelPattern (pv, str, pvs) ->
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
                let diffs_for_nmd_type t =
                    if Synthesis.is_model_dependent_type t then Set.empty
                    else
                        let couples = Model.all_values_ext infos [t;t]
                        let couples = Seq.map Helper.lst_to_couple couples
                        let couples = Seq.filter (fun (a,b) -> not (value_equal a b)) couples
                        Set.ofSeq couples
                let nmd_diffs = diffs_for_nmd_type Bool
                Set.fold aux Set.empty (Set.union diffs nmd_diffs)

        let all_dicos_matching_free_var vars prev_dico =
            let is_free_var (d:VarDecl) =
                if Map.containsKey d.Name prev_dico then false
                else true
            let free_vars = Set.toList (Set.filter is_free_var vars)
            let free_types = List.map (fun (v:VarDecl) -> v.Type) free_vars
            let all_values = Model.all_values_ext infos free_types
            let aux dico free_vars cvs =
                List.fold2 (fun acc (v:VarDecl) cv -> Map.add v.Name cv acc) dico free_vars cvs
            Seq.map (aux prev_dico free_vars) all_values

        let add_constraint dico (diffs,mv,mf) r =
            let resolve pv =
                match pv with
                | PatternConst b -> ConstBool b
                | PatternVar str -> Map.find str dico
            match r with
            | VarPattern (_,str) -> (diffs,Set.add str mv,mf)
            | RelPattern (_,str,pvs) ->
                let cvs = List.map resolve pvs
                (diffs,mv,Set.add (str,cvs) mf)
            | ValueDiffPattern (_, pv1, pv2) ->
                let cv1 = resolve pv1
                let cv2 = resolve pv2
                (add_diff_constraint diffs cv1 cv2,mv,mf)

        let add_constraints dico cfg rs =
            Set.fold (add_constraint dico) cfg rs

        let step (diffs, mv, mf) impls
            (already_applied:System.Collections.Generic.Dictionary<Set<Pattern> * Map<string, ConstValue>, unit>) =
            // Apply implication rules one time
            let aux (diffs,mv,mf) (ls,rs) =
                let rec all_dicos ls =
                    match ls with
                    | [] -> Seq.singleton Map.empty
                    | l::ls ->
                        let dicos = all_dicos ls
                        Seq.concat (Seq.map (all_dicos_matching_pattern (diffs,mv,mf) l) dicos)
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
                Seq.fold (fun acc dico -> add_constraints dico acc rs) (diffs,mv,mf) dicos

            let (diffs,mv,mf) = List.fold aux (diffs,mv,mf) impls
            (diffs, mv, mf)

        let closure diffs mv mf end_condition =
            // Separate rules
            let impls_base = List.filter (fun (ls, _) -> Set.isEmpty ls) impls
            let impls = List.filter (fun (ls, _) -> not (Set.isEmpty ls)) impls

            // Apply base rules
            let already_applied =
                System.Collections.Generic.Dictionary<Set<Pattern> * Map<string, ConstValue>, unit>()
            let (diffs, mv, mf) = step (diffs, mv, mf) impls_base already_applied

            // Apply other rules until fixpoint
            let step_fp (diffs, mv, mf) =
                let already_applied =
                    System.Collections.Generic.Dictionary<Set<Pattern> * Map<string, ConstValue>, unit>()
                let rec aux (diffs, mv, mf) =
                    let next = step (diffs, mv, mf) impls already_applied
                    if end_condition next then raise EndCondition
                    else if next = (diffs, mv, mf) then next else aux next
                aux (diffs, mv, mf)
            let (diffs, mv, mf) = step_fp (diffs, mv, mf)
            (diffs, mv, mf)

        let mf = m.f
        let mv = m.v
        let diffs = m.d
        // Remove useless vars
        let remove_rel_if_useless acc var =
            (*if (Map.find var decls.v).Type <> Bool // Uncomment if all rules target boolean vars
            then acc
            else*)
                let acc' = Set.remove var acc
                try
                    ignore (closure diffs acc' mf (fun (_,cl,_) -> Set.contains var cl))
                    acc
                with :? EndCondition -> acc'
        let mv = Set.fold remove_rel_if_useless mv mv

        // Remove useless relations
        let remove_rel_if_useless acc rel =
            (*let (str,_) = rel
            if (Map.find str decls.f).Output <> Bool // Uncomment if all rules target relations
            then acc
            else*)
                let acc' = Set.remove rel acc
                try
                    ignore (closure diffs mv acc' (fun (_,_,cl) -> Set.contains rel cl))
                    acc
                with :? EndCondition -> acc'
        let mf = Set.fold remove_rel_if_useless mf mf

        // Remove useless diff
        let remove_diff_if_useless acc (v1,v2) =
            let acc' = remove_diff_constraint acc v1 v2
            try
                ignore (closure acc' mv mf (fun (cl,_,_) -> value_diff cl v1 v2))
                acc
            with :? EndCondition -> acc'
        let diffs = Set.fold remove_diff_if_useless diffs diffs
        
        // Result
        { Synthesis.v = mv ; Synthesis.f = mf ; Synthesis.d = diffs }

    type ValueAssociation =
        | VAConst of ConstValue
        | New of string
        | ExistingVar of string
        | ExistingFun of string * List<ConstValue>

    let formula_from_marks (env:Model.Environment) (m:Synthesis.Marks)
        (alt_exec:List<Synthesis.Marks*Model.Environment>) =
      
        // Associate a var to each value
        let next_name_nb = ref 0
        let new_var_name () =
            let c = (char)(65 + !next_name_nb)
            next_name_nb := !next_name_nb + 1
            c.ToString()
            
        let vars_map = ref Map.empty

        // Associates an existing variable to a value
        let associate_existing_var (env:Model.Environment) str =
            let cv = Map.find str env.v
            if not (Map.containsKey cv !vars_map) then
                vars_map := Map.add cv (ExistingVar str) !vars_map

        // Associates an existing function to a value
        let associate_existing_fun (env:Model.Environment) (str,cvs) =
            let cv = Map.find (str,cvs) env.f
            if not (Map.containsKey cv !vars_map) then
                vars_map := Map.add cv (ExistingFun (str, cvs)) !vars_map

        // Return the associated var or CREATES a new existentially quantified var
        let value2var cv =
            match cv with
            | cv when not (Synthesis.is_model_dependent_value cv) -> VAConst cv
            | cv ->
                try
                    Map.find cv !vars_map
                with :? System.Collections.Generic.KeyNotFoundException ->
                    let name = new_var_name ()
                    vars_map := Map.add cv (New name) !vars_map
                    New name

        let value_assigned cv =
            match cv with
            | cv when not (Synthesis.is_model_dependent_value cv) -> false
            | cv -> Map.containsKey cv !vars_map

        let all_new_vars_decl_assigned () : Set<VarDecl> =
            let content = (Map.toList !vars_map)
            let content = List.filter (fun (_,assoc) -> match assoc with New _ -> true | _ -> false) content
            let vars =
                List.map
                    (fun (cv,assoc) ->
                        match assoc with
                        | New str -> AST.default_var_decl str (type_of_const_value cv)
                        | _ -> failwith "Invalid association."
                    ) content
            Set.ofList vars

        let rec value_of_association va =
            match va with
            | VAConst cv -> ValueConst cv
            | New str -> ValueVar str
            | ExistingVar str -> ValueVar str
            | ExistingFun (str, cvs) ->
                let vs = List.map (fun cv -> value_of_association (value2var cv)) cvs
                ValueFun (str, vs)

        let constraints_for (m:Synthesis.Marks,env:Model.Environment) =
            // Browse the constraints to associate an existing var to values when possible
            Set.iter (associate_existing_var env) m.v
            let v' = // We remove trivial equalities
                Set.filter
                    (
                        fun str ->
                            let cv = Map.find str env.v
                            value2var cv <> ExistingVar str
                    ) m.v
            let m = {m with v=v'}

            // Browse the constraints to associate an existing fun to values when possible
            Set.iter (associate_existing_fun env) m.f
            let f' = // We remove trivial equalities
                Set.filter
                    (
                        fun (str, cvs) ->
                            let cv = Map.find (str, cvs) env.f
                            value2var cv <> ExistingFun (str, cvs)
                    ) m.f
            let m = {m with f=f'}

            // Replace value by var in each var/fun marked constraint
            let constraints_var =
                Set.map
                    (
                        fun str ->
                            let cv = Map.find str env.v
                            ValueEqual (ValueVar str, value_of_association (value2var cv))
                    ) m.v
            let constraints_fun =
                Set.map
                    (
                        fun (str,cvs) ->
                            let cv = Map.find (str,cvs) env.f
                            let cvs = List.map (fun cv -> value_of_association (value2var cv)) cvs
                            ValueEqual (ValueFun (str, cvs), value_of_association (value2var cv))
                    ) m.f
            let constraints = Set.union constraints_var constraints_fun

            // Add inequalities between vars
            let ineq_constraints = // We don't need inequalities when one of the member is unused
                Set.filter (fun (cv1,cv2) -> value_assigned cv1 && value_assigned cv2) m.d
            let ineq_constraints =
                Set.map
                    (
                        fun (cv1,cv2) ->
                            let (cv1,cv2) = Helper.order_tuple (cv1,cv2)
                            ValueNot (ValueEqual (value_of_association (value2var cv1), value_of_association (value2var cv2)))
                    ) ineq_constraints
            let constraints = Set.union constraints ineq_constraints
            constraints

        let constraints = constraints_for (m, env)
        let vars = all_new_vars_decl_assigned ()

        let alt_constraints =
            List.map 
                (fun e ->
                    let c = constraints_for e
                    (c, all_new_vars_decl_assigned ())
                ) alt_exec
        let alt_constraints = List.rev alt_constraints

        let formula_for cs vars =
            let cs = Set.toList cs
            match cs with
            | [] -> ValueConst (ConstBool true)
            | h::constraints ->
                let formula = List.fold (fun acc c -> ValueAnd (acc,c)) h constraints
                Set.fold (fun acc vd -> ValueExists (vd, acc)) formula vars

        let (formulas, _) =
            List.fold
                (fun (formulas, declared_vars) (c, vars) ->
                    let f = formula_for c (Set.difference vars declared_vars)
                    (f::formulas, vars)
                ) ([], vars) alt_constraints

        let formulas =
            match formulas with
            | [] ->  ValueConst (ConstBool false)
            | h::formulas -> List.fold (fun acc c -> ValueOr (acc,c)) h formulas

        // Construct the formula with the quantifiers
        let constraints = Set.toList constraints
        match constraints with
        | [] -> ValueConst (ConstBool true)
        | h::constraints ->
            let formula = List.fold (fun acc c -> ValueAnd (acc,c)) h constraints
            let formula = ValueImply (formula, formulas)
            Set.fold (fun acc vd -> ValueForall (vd, acc)) formula vars

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
        | ValueNot (ValueOr (f1, f2)) -> simplify_value (ValueAnd (ValueNot f1, ValueNot f2))
        | ValueNot (ValueAnd (f1, f2)) -> simplify_value (ValueOr (ValueNot f1, ValueNot f2))
        | ValueNot (ValueForall (d,f)) -> simplify_value (ValueExists (d, ValueNot f))
        | ValueNot (ValueExists (d,f)) -> simplify_value (ValueForall (d, ValueNot f))
        | ValueNot (ValueImply (f1, f2)) -> simplify_value (ValueAnd (f1, ValueNot f2))
        // Identity cases
        | ValueConst b -> ValueConst b
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
        | ValueInterpreted (str, vs) -> ValueInterpreted (str, List.map simplify_value vs)
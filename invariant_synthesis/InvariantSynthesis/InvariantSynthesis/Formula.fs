﻿module Formula

    open AST

    let order_tuple (a,b) =
        if a < b then (a,b) else (b,a)

    exception DoesntMatch

    let simplify_marks infos (impls:List<AST.ImplicationRule>) (decls:Model.Declarations) (env:Model.Environment) (m:Synthesis.Marks) (ad:Synthesis.AdditionalData) =

        let value_equal cv1 cv2 = Interpreter.value_equal infos cv1 cv2

        let value_diff diffs cv1 cv2 =
            if Synthesis.is_model_dependent_value cv1 && Synthesis.is_model_dependent_value cv2
            then Set.contains (cv1,cv2) diffs || Set.contains (cv2,cv1) diffs
            else value_equal cv1 cv2

        let add_diff_constraint diffs cv1 cv2 =
            Set.add (cv2,cv1) (Set.add (cv1,cv2) diffs)

        let remove_diff_constraint diffs cv1 cv2 =
            Set.remove (cv2,cv1) (Set.remove (cv1,cv2) diffs)

        let free_vars_of_pattern p =
            let aux acc t v =
                match v with
                | PatternVar name ->
                    Set.add ({Name=name;Type=t;Representation=default_representation}) acc
                | PatternConst _ -> acc
            match p with
            | VarPattern _ -> Set.empty
            | RelPattern (_, str, vs) ->
                let types = (Map.find str decls.f).Input
                List.fold2 aux Set.empty types vs
            | ValueDiffPattern (type_str,n1,n2) ->
                let t = Uninterpreted type_str
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
            | ValueDiffPattern (type_str, pv1, pv2) ->
                let t = Uninterpreted type_str
                let aux acc (cv1,cv2) =
                    if t <> type_of_const_value cv1 || t <> type_of_const_value cv2 then acc
                    else
                        try
                            let dico = update_dico prev_dico pv1 cv1
                            Set.add (update_dico dico pv2 cv2) acc
                        with :? DoesntMatch -> acc
                Set.fold aux Set.empty diffs

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

        let step (diffs, mv, mf) impls =
            // Apply implication rules one time
            let aux (diffs,mv,mf) (ls,rs) =
                let rec all_dicos ls =
                    match ls with
                    | [] -> Seq.singleton (Map.empty)
                    | l::ls ->
                        let dicos = all_dicos ls
                        Seq.concat (Seq.map (all_dicos_matching_pattern (diffs,mv,mf) l) dicos)
                let free_vars = free_vars_of_patterns (Set.union ls rs)
                let dicos = all_dicos (Set.toList ls)
                let dicos = Seq.concat (Seq.map (all_dicos_matching_free_var free_vars) dicos)
                Seq.fold (fun acc dico -> add_constraints dico acc rs) (diffs,mv,mf) dicos

            let (diffs,mv,mf) = List.fold aux (diffs,mv,mf) impls
            (diffs, mv, mf)

        let closure diffs mv mf =
            // Separate rules
            let impls_base = List.filter (fun (ls, _) -> Set.isEmpty ls) impls
            let impls = List.filter (fun (ls, _) -> not (Set.isEmpty ls)) impls

            // Apply base rules
            let (diffs, mv, mf) = step (diffs, mv, mf) impls_base

            // Apply other rules until fixpoint
            let rec step_fp (diffs, mv, mf) =
                let next = step (diffs, mv, mf) impls
                if next = (diffs, mv, mf) then next else step_fp next
            let (diffs, mv, mf) = step_fp (diffs, mv, mf)
            (diffs, mv, mf)

        let mf = m.f
        let mv = m.v
        let diffs = ad.d
        // Remove useless vars
        let remove_rel_if_useless acc var =
            if (Map.find var decls.v).Type <> Bool // All flags/rules target boolean vars
            then acc
            else
                let acc' = Set.remove var acc
                let (_, cl, _) = closure diffs acc' mf
                if Set.contains var cl
                then acc'
                else acc
        let mv = Set.fold remove_rel_if_useless mv mv

        // Remove useless relations
        let remove_rel_if_useless acc rel =
            let (str,_) = rel
            if (Map.find str decls.f).Output <> Bool // All flags/rules target relations
            then acc
            else
                let acc' = Set.remove rel acc
                let (_, _, cl) = closure diffs mv acc'
                if Set.contains rel cl
                then acc'
                else acc
        let mf = Set.fold remove_rel_if_useless mf mf

        // Remove useless diff
        let remove_diff_if_useless acc (v1,v2) =
            let acc' = remove_diff_constraint acc v1 v2
            let (cl, _, _) = closure acc' mv mf
            if value_diff cl v1 v2
            then acc'
            else acc
        let diffs = Set.fold remove_diff_if_useless diffs diffs
        
        // Result
        let ad = { ad with d=diffs }
        let m = { m with f=mf ; v=mv }
        (m, ad)

    type ValueAssociation =
        | VAConst of ConstValue
        | New of string
        | ExistingVar of string
        | ExistingFun of string * List<ConstValue>

    let formula_from_marks (env:Model.Environment) (m:Synthesis.Marks) (ad:Synthesis.AdditionalData) =
      
        // Associate a var to each value
        let next_name_nb = ref 0
        let new_var_name () =
            let c = (char)(65 + !next_name_nb)
            next_name_nb := !next_name_nb + 1
            c.ToString()
            
        let vars_map = ref Map.empty

        // Associates an existing variable to a value
        let associate_existing_var str =
            let cv = Map.find str env.v
            if not (Map.containsKey cv !vars_map) then
                vars_map := Map.add cv (ExistingVar str) !vars_map

        // Associates an existing function to a value
        let associate_existing_fun (str,cvs) =
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

        let all_new_vars_decl_assigned () : List<VarDecl> =
            let content = (Map.toList !vars_map)
            let content = List.filter (fun (_,assoc) -> match assoc with New _ -> true | _ -> false) content
            List.map (fun (cv,assoc) -> match assoc with New str -> { Name=str ; Type=type_of_const_value cv ; Representation=default_representation } | _ -> failwith "Invalid association.") content

        let rec value_of_association va =
            match va with
            | VAConst cv -> ValueConst cv
            | New str -> ValueVar str
            | ExistingVar str -> ValueVar str
            | ExistingFun (str, cvs) ->
                let vs = List.map (fun cv -> value_of_association (value2var cv)) cvs
                ValueFun (str, vs)

        // Browse the constraints to associate an existing var to values when possible
        Set.iter (associate_existing_var) m.v
        let v' = // We remove trivial equalities
            Set.filter
                (
                    fun str ->
                        let cv = Map.find str env.v
                        value2var cv <> ExistingVar str
                ) m.v
        let m = {m with v=v'}

        // Browse the constraints to associate an existing fun to values when possible
        Set.iter (associate_existing_fun) m.f
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
                        Equal (ValueVar str, value_of_association (value2var cv))
                ) m.v
        let constraints_fun =
            Set.map
                (
                    fun (str,cvs) ->
                        let cv = Map.find (str,cvs) env.f
                        let cvs = List.map (fun cv -> value_of_association (value2var cv)) cvs
                        Equal (ValueFun (str, cvs), value_of_association (value2var cv))
                ) m.f
        let constraints = Set.union constraints_var constraints_fun

        // Add inequalities between vars
        let ineq_constraints = // We don't need inequalities when one of the member is unused
            Set.filter (fun (cv1,cv2) -> value_assigned cv1 && value_assigned cv2) ad.d
        let ineq_constraints =
            Set.map
                (
                    fun (cv1,cv2) ->
                        let (cv1,cv2) = order_tuple (cv1,cv2)
                        Not (Equal (value_of_association (value2var cv1), value_of_association (value2var cv2)))
                ) ineq_constraints
        let constraints = Set.union constraints ineq_constraints

        // Construct the formula with the quantifiers
        let constraints = Set.toList constraints
        match constraints with
        | [] -> Const true
        | h::constraints ->
            let formula = List.fold (fun acc c -> And (acc,c)) h constraints
            let vars = all_new_vars_decl_assigned ()
            List.fold (fun acc vd -> Exists (vd, acc)) formula vars

    let rec simplify_formula f =
        match f with
        // Negation
        | Not (Equal (v, ValueConst (ConstBool b)))
        | Not (Equal (ValueConst (ConstBool b), v))
            -> simplify_formula (Equal (v, ValueConst (ConstBool (not b))))
        | Not (Const b) -> simplify_formula (Const (not b))
        | Not (Not f) -> simplify_formula f
        | Not (Or (f1, f2)) -> simplify_formula (And (Not f1, Not f2))
        | Not (And (f1, f2)) -> simplify_formula (Or (Not f1, Not f2))
        | Not (Forall (d,f)) -> simplify_formula (Exists (d, Not f))
        | Not (Exists (d,f)) -> simplify_formula (Forall (d, Not f))
        // Identity cases
        | Const b -> Const b
        | Equal (v1, v2) -> Equal (v1, v2)
        | Or (f1, f2) -> Or (simplify_formula f1, simplify_formula f2)
        | And (f1, f2) -> And (simplify_formula f1, simplify_formula f2)
        | Not f -> Not (simplify_formula f)
        | Forall (v, f) -> Forall (v, simplify_formula f)
        | Exists (v, f) -> Exists (v, simplify_formula f)

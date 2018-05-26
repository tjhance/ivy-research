module Formula

    open AST
    open Synthesis
    open System.Net.Mail
    open System.Net.Mail

    let order_tuple (a,b) =
        if a < b then (a,b) else (b,a)

    let simplify_marks infos (impls:List<AST.ImplicationRule>) (decls:Model.Declarations) (env:Model.Environment) (m:Synthesis.Marks) (ad:Synthesis.AdditionalData) =

        let value_equal cv1 cv2 = Interpreter.value_equal infos cv1 cv2

        let value_diff diffs cv1 cv2 =
            Set.contains (cv1,cv2) diffs || Set.contains (cv2,cv1) diffs

        let couple_of_lst lst =
            let cv1 = (List.head lst)
            let cv2 = List.head (List.tail lst)
            (cv1, cv2)

        let add_diff_constraint diffs cv1 cv2 =
            Set.add (cv2,cv1) (Set.add (cv1,cv2) diffs)

        let remove_diff_constraint diffs cv1 cv2 =
            Set.remove (cv2,cv1) (Set.remove (cv1,cv2) diffs)

        let rec transitive_closure pairs =
            let step pairs =
                let aux acc (l,r) =
                    let aux' acc (l',r') =
                        let acc = if r'=l then Set.add (l',r) acc else acc
                        let acc = if r=l' then Set.add (l,r') acc else acc
                        acc
                    Set.fold aux' acc acc
                Set.fold aux pairs pairs
            let next = step pairs
            if next = pairs then next else transitive_closure next

        let transitive_closure_of_rel str value rels =

            let is_related_rel (str', cvs') =
                if str <> str'
                then false
                else Map.find (str', cvs') env.f = ConstBool value

            let rel_pairs = Set.filter is_related_rel rels
            let rel_pairs = Set.map (fun (_, cvs') -> couple_of_lst cvs') rel_pairs
            let trans = transitive_closure rel_pairs
            Set.map (fun (cv1,cv2) -> (str,[cv1;cv2])) trans

        let closure diffs mv mf =
            // Reflexion
            let aux acc (_, (d:FunDecl)) =
                if Set.contains Reflexive d.Flags || Set.contains Reflexive d.NegFlags
                then
                    let values = Model.all_values infos (List.head d.Input)
                    let to_add = Seq.map (fun v -> (d.Name, List.map (fun _ -> v) d.Input)) values
                    Set.union acc (Set.ofSeq to_add)
                else acc
            let mf = List.fold aux mf (Map.toList decls.f)

            let rec step_fp (diffs, mv, mf) =
                // Step
                let step (diffs, mv, mf) =
                    // Impls
                    let aux (diffs,mv,mf) (l,rs) =
                        let add_constraint dico (diffs,mv,mf) r =
                            match r with
                            | VarPattern (_,str) -> (diffs,Set.add str mv,mf)
                            | RelPattern (_,str,strs) ->
                                let cvs = List.map (fun str -> Map.find str dico) strs
                                (diffs,mv,Set.add (str,cvs) mf)
                            | ValueDiffPattern (str1, str2) ->
                                let cv1 = Map.find str1 dico
                                let cv2 = Map.find str2 dico
                                (add_diff_constraint diffs cv1 cv2,mv,mf)
                        let add_constraints dico cfg rs =
                            Set.fold (add_constraint dico) cfg rs
                        match l with
                        | VarPattern (b,str) ->
                            if Set.contains str mv && Map.find str env.v = ConstBool b
                            then add_constraints Map.empty (diffs,mv,mf) rs
                            else (diffs,mv,mf)
                        | RelPattern (b,str,strs) ->
                            let is_involved (str',cvs') =
                                if str' <> str then false
                                else
                                    Map.find (str',cvs') env.f = ConstBool b
                            let assign_dico strs cvs =
                                List.fold2 (fun acc str cv -> Map.add str cv acc) Map.empty strs cvs
                            let candidates = Set.filter is_involved mf
                            let candidates = Set.map (fun (_, cvs) -> assign_dico strs cvs) candidates
                            Set.fold (fun acc dico -> add_constraints dico acc rs) (diffs,mv,mf) candidates
                        | ValueDiffPattern (str1, str2) ->
                            let assign_dico (cv1, cv2) =
                                Map.add str1 cv1 (Map.add str2 cv2 Map.empty)
                            let candidates = Set.map assign_dico diffs
                            Set.fold (fun acc dico -> add_constraints dico acc rs) (diffs,mv,mf) candidates
                    let (diffs,mv,mf) = List.fold aux (diffs,mv,mf) impls
                    // Transitive closure
                    let aux acc (_, (d:FunDecl)) =
                        let acc =
                            if Set.contains Transitive d.Flags
                            then
                                let tr = transitive_closure_of_rel d.Name true acc
                                Set.union acc tr
                            else acc
                        if Set.contains Transitive d.NegFlags
                        then
                            let tr = transitive_closure_of_rel d.Name false acc
                            Set.union acc tr
                        else acc
                    let mf = List.fold aux mf (Map.toList decls.f)
                    // Symetry
                    let aux acc (str, cvs) =
                        let d = Map.find str decls.f
                        let v = Map.find (str, cvs) env.f
                        if (Set.contains Symetric d.Flags && v = ConstBool true)
                            || (Set.contains Symetric d.NegFlags && v = ConstBool false)
                        then Set.add (str, List.rev cvs) acc
                        else acc
                    let mf = Set.fold aux mf mf
                    // Anti-symetry
                    let aux acc (str, cvs) =
                        let d = Map.find str decls.f
                        let v = Map.find (str, cvs) env.f
                        if (Set.contains AntiSymetric d.Flags && v = ConstBool true)
                            || (Set.contains AntiSymetric d.NegFlags && v = ConstBool false)
                        then
                            let (cv1, cv2) = couple_of_lst cvs
                            if value_diff diffs cv1 cv2
                            then Set.add (str, List.rev cvs) acc
                            else acc
                        else acc
                    let mf = Set.fold aux mf mf
                    // Diffs
                    let aux acc (str, cvs) =
                        let d = Map.find str decls.f
                        let v = Map.find (str, cvs) env.f
                        if (Set.contains Reflexive d.Flags && v = ConstBool false)
                            || (Set.contains Reflexive d.NegFlags && v = ConstBool true)
                        then
                            let (cv1, cv2) = couple_of_lst cvs
                            if value_equal cv1 cv2
                            then add_diff_constraint acc cv1 cv2
                            else acc
                        else acc
                    let diffs = Set.fold aux diffs mf
                    (diffs, mv, mf)

                let next = step (diffs, mv, mf)
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

    let type_of_const_value cv =
        match cv with
        | ConstVoid -> Void
        | ConstBool _ -> Bool
        | ConstInt (s,_) -> Uninterpreted s

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

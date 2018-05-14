module Formula

    open AST

    let order_tuple (a,b) =
        if a < b then (a,b) else (b,a)

    let type_of_const_value cv =
        match cv with
        | ConstVoid -> Void
        | ConstBool _ -> Bool
        | ConstInt (s,_) -> Uninterpreted s

    let formula_from_marks (env:Model.Environment) (m:Synthesis.Marks) (ad:Synthesis.AdditionalData) =
        // Associate a var to each value
        let next_name_nb = ref 0
        let new_var_name () =
            let c = (char)(65 + !next_name_nb)
            next_name_nb := !next_name_nb + 1
            c.ToString()

        let vars_map = ref Map.empty

        // Associates an existing var to a value if the constraint allows it
        let associate_existing_var str =
            let cv = Map.find str env.v
            vars_map := Map.add cv (str, false) !vars_map

        // Return the associated var or CREATES a new existentially quantified var
        let value2var cv =
            match cv with
            | cv when not (Synthesis.is_model_dependent_value cv) -> ValueConst cv
            | cv ->
                try
                    let (str, _) = Map.find cv !vars_map
                    ValueVar (str)
                with :? System.Collections.Generic.KeyNotFoundException ->
                    let name = new_var_name ()
                    vars_map := Map.add cv (name, true) !vars_map
                    ValueVar name

        let value_assigned cv =
            match cv with
            | cv when not (Synthesis.is_model_dependent_value cv) -> false
            | cv -> Map.containsKey cv !vars_map

        let all_new_vars_decl_assigned () : List<VarDecl> =
            let content = (Map.toList !vars_map)
            let content = List.filter (fun (_,(_,b)) -> b) content
            List.map (fun (cv,(v,_)) -> { Name=v ; Type=type_of_const_value cv }) content

        // Browse the constraints to associate an existing var to values when possible
        Set.iter (associate_existing_var) m.v
        let v' = // We remove trivial equalities
            Set.filter
                (
                    fun str ->
                        let cv = Map.find str env.v
                        value2var cv <> ValueVar str
                ) m.v
        let m = {m with v=v'}

        // Replace value by var in each var/fun marked constraint
        let constraints_var =
            Set.map
                (
                    fun str ->
                        let cv = Map.find str env.v
                        Equal (ValueVar str, value2var cv)
                ) m.v
        let constraints_fun =
            Set.map
                (
                    fun (str,cvs) ->
                        let cv = Map.find (str,cvs) env.f
                        let cvs = List.map value2var cvs
                        Equal (ValueFun (str, cvs), value2var cv)
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
                        Not (Equal (value2var cv1, value2var cv2))
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

    ////////////////////////////////////////////////////////////////////////

    let const_value_to_string cv =
        match cv with
        | ConstVoid -> "()"
        | ConstBool b -> sprintf "%b" b
        | ConstInt (_,i) -> sprintf "%i" i

    let type_to_string t =
        match t with
        | Void -> "void"
        | Bool -> "bool"
        | Uninterpreted str -> str

    let var_decl_to_string (vd:VarDecl) = sprintf "%s:%s" vd.Name (type_to_string vd.Type)

    let list_to_args_str lst =
        match lst with
        | [] -> "()"
        | h::lst -> sprintf "(%s)" (List.fold (sprintf "%s, %s") h lst)

    let add_parenthesis_if_needed str prec env_prec =
        if prec < env_prec
        then sprintf "(%s)" str
        else str

    let rec value_to_string v =
        match v with
        | ValueConst cv -> const_value_to_string cv
        | ValueVar str -> str
        | ValueFun (str, vs) -> sprintf "%s%s" str (list_to_args_str (List.map value_to_string vs))
        | ValueEqual (v1,v2) -> sprintf "(%s == %s)" (value_to_string v1) (value_to_string v2)
        | ValueOr (v1,v2) -> sprintf "(%s || %s)" (value_to_string v1) (value_to_string v2)
        | ValueAnd (v1,v2) -> sprintf "(%s && %s)" (value_to_string v1) (value_to_string v2)
        | ValueNot v -> sprintf "not %s" (value_to_string v)
        | ValueSomeElse (d,f,v) -> sprintf "some %s s.t. %s or %s" (var_decl_to_string d) (formula_to_string f 10) (value_to_string v)

    and formula_to_string f prec =
        match f with
        | Const b -> sprintf "%b" b
        | Equal (v1, v2) ->
            let str = sprintf "%s = %s" (value_to_string v1) (value_to_string v2)
            add_parenthesis_if_needed str 4 prec
        | Or (f1,f2) ->
            let str = sprintf "%s | %s" (formula_to_string f1 2) (formula_to_string f2 2)
            add_parenthesis_if_needed str 2 prec
        | And (f1,f2) ->
            let str = sprintf "%s & %s" (formula_to_string f1 3) (formula_to_string f2 3)
            add_parenthesis_if_needed str 3 prec
        | Not f ->
            let str = sprintf "~%s" (formula_to_string f 5)
            add_parenthesis_if_needed str 5 prec
        | Forall (vd, f) ->
            let str = sprintf "F %s. %s" (var_decl_to_string vd) (formula_to_string f 1)
            add_parenthesis_if_needed str 1 prec
        | Exists (vd, f) ->
            let str = sprintf "E %s. %s" (var_decl_to_string vd) (formula_to_string f 1)
            add_parenthesis_if_needed str 1 prec

(*
Precedence:
value : oo
~ : 5
= : 4
& : 3
| : 2
F E : 1
*)

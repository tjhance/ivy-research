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
        let value2var cv =
            match cv with
            | cv when not (Synthesis.is_model_dependent_value cv) -> ValueConst cv
            | cv ->
                try
                    ValueVar (Map.find cv !vars_map)
                with :? System.Collections.Generic.KeyNotFoundException ->
                    let name = new_var_name ()
                    vars_map := Map.add cv name !vars_map
                    ValueVar name

        let value_assigned cv =
            match cv with
            | cv when not (Synthesis.is_model_dependent_value cv) -> false
            | cv -> Map.containsKey cv !vars_map

        let all_vars_decl_assigned () : List<VarDecl> =
            let content = (Map.toList !vars_map)
            List.map (fun (cv,v) -> { Name=v ; Type=type_of_const_value cv }) content

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
            let vars = all_vars_decl_assigned ()
            List.fold (fun acc vd -> Exists (vd, acc)) formula vars

        // TODO: Simplify formula (don't quantify on variable equal to a value/function)
        // TODO: Improve printing (consider conjonctions as a list, etc)

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

    let rec value_to_string v =
        match v with
        | ValueConst cv -> const_value_to_string cv
        | ValueVar str -> str
        | ValueFun (str, vs) -> sprintf "%s%s" str (list_to_args_str (List.map value_to_string vs))
        | ValueEqual (v1,v2) -> sprintf "%s == %s" (value_to_string v1) (value_to_string v2)
        | ValueOr (v1,v2) -> sprintf "(%s || %s)" (value_to_string v1) (value_to_string v2)
        | ValueAnd (v1,v2) -> sprintf "(%s && %s)" (value_to_string v1) (value_to_string v2)
        | ValueNot v -> sprintf "not(%s)" (value_to_string v)

    let rec formula_to_string f =
        match f with
        | Const b -> sprintf "%b" b
        | Equal (v1, v2) -> sprintf "%s = %s" (value_to_string v1) (value_to_string v2)
        | Or (f1,f2) -> sprintf "(%s | %s)" (formula_to_string f1) (formula_to_string f2)
        | And (f1,f2) -> sprintf "(%s & %s)" (formula_to_string f1) (formula_to_string f2)
        | Not f -> sprintf "~(%s)" (formula_to_string f)
        | Forall (vd, f) -> sprintf "F %s. %s" (var_decl_to_string vd) (formula_to_string f)
        | Exists (vd, f) -> sprintf "E %s. %s" (var_decl_to_string vd) (formula_to_string f)

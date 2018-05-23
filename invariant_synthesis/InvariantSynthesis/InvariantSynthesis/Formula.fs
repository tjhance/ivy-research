module Formula

    open AST
    open System.Runtime.InteropServices.ComTypes

    // TODO: 2steps synthesis

    let order_tuple (a,b) =
        if a < b then (a,b) else (b,a)

    let simplify_marks (decls:Model.Declarations) (env:Model.Environment) (m:Synthesis.Marks) (ad:Synthesis.AdditionalData) =

        let value_equal cv1 cv2 = Interpreter.value_equal () cv1 cv2

        let value_diff diffs cv1 cv2 =
            Set.contains (cv1,cv2) diffs || Set.contains (cv2,cv1) diffs

        let add_diff_constraint diffs cvs =
            let cv1 = (List.head cvs)
            let cv2 = List.head (List.tail cvs)
            Set.add (cv2,cv1) (Set.add (cv1,cv2) diffs)

        let diffs_implied (m:Synthesis.Marks) =
            let aux acc (str, cvs) =
                if List.length cvs <> 2 then acc
                else
                    let flags = (Map.find str decls.f).Flags
                    let value = Map.find (str, cvs) env.f
                    if Set.contains Strict flags && value = ConstBool true
                    then add_diff_constraint acc cvs
                    else if Set.contains Reflexive flags && value = ConstBool false
                    then add_diff_constraint acc cvs
                    else acc
            Set.fold aux Set.empty m.f

        let is_relation_useful diffs rels (str, cvs) =
            if List.length cvs <> 2 then true
            else
                let cv1 = List.head cvs
                let cv2 = List.head (List.tail cvs)
                let flags = (Map.find str decls.f).Flags
                let value = Map.find (str, cvs) env.f
                match value with
                | ConstBool true ->
                    if Set.contains Reflexive flags && value_equal cv1 cv2
                    then false
                    else
                        // TODO: case of the transitive flag
                        true
                | ConstBool false ->
                    if  Set.contains Strict flags && value_equal cv1 cv2
                    then false
                    else true
                | _ -> true

        // Remove useless diff
        let di = diffs_implied m
        let d' = Set.difference ad.d di
        let all_d = Set.union ad.d di

        // Remove useless relations
        let mf' = Set.filter (is_relation_useful all_d m.f) m.f
        
        // Result
        let ad = { ad with d=d' }
        let m = { m with f=mf' }
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

    let formula_from_marks (decls:Model.Declarations) (env:Model.Environment) (m:Synthesis.Marks) (ad:Synthesis.AdditionalData) =
        let (m, ad) = simplify_marks decls env m ad
        
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

    ////////////////////////////////////////////////////////////////////////

    let rec simplify_formula f =
        match f with
        // Negation
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

    let var_decl_to_string (vd:VarDecl) =
        match vd.Representation.DisplayName with
        | None -> sprintf "%s:%s" vd.Name (type_to_string vd.Type)
        | Some s -> sprintf "%s:%s" s (type_to_string vd.Type)

    let list_to_args_str lst =
        match lst with
        | [] -> "()"
        | h::lst -> sprintf "(%s)" (List.fold (sprintf "%s, %s") h lst)

    let add_parenthesis_if_needed str prec env_prec =
        if prec < env_prec
        then sprintf "(%s)" str
        else str

    let rec value_to_string (decls:Model.Declarations) v =
        let rec aux v =
            match v with
            | ValueConst cv -> const_value_to_string cv
            | ValueVar str ->
                try
                    match (Map.find str decls.v).Representation.DisplayName with
                    | None -> str
                    | Some str -> str
                with :? System.Collections.Generic.KeyNotFoundException -> str
            | ValueFun (str, vs) ->
                try
                    let d = Map.find str decls.f
                    let str = 
                        match d.Representation.DisplayName with
                        | None -> str
                        | Some str -> str
                    if Set.contains Infix d.Representation.Flags
                    then sprintf "%s %s %s" (aux (List.head vs)) str (aux (List.head (List.tail vs)))
                    else sprintf "%s%s" str (list_to_args_str (List.map aux vs))
                with :? System.Collections.Generic.KeyNotFoundException ->
                    sprintf "%s%s" str (list_to_args_str (List.map aux vs))
            | ValueEqual (v1,v2) -> sprintf "(%s == %s)" (aux v1) (aux v2)
            | ValueOr (v1,v2) -> sprintf "(%s || %s)" (aux v1) (aux v2)
            | ValueAnd (v1,v2) -> sprintf "(%s && %s)" (aux v1) (aux v2)
            | ValueNot v -> sprintf "not %s" (aux v)
            | ValueSomeElse (d,f,v) ->
                let decls = Model.add_var_declaration d decls
                sprintf "some %s s.t. %s or %s" (var_decl_to_string d) (formula_to_string decls f 10) (aux v)
        aux v

    and formula_to_string decls f prec =
        match f with
        // ----- Syntaxic sugars -----
        | Not (Equal (v1,v2)) ->
            let str = sprintf "%s ~= %s" (value_to_string decls v1) (value_to_string decls v2)
            add_parenthesis_if_needed str 4 prec
        | Equal (v, ValueConst (ConstBool true))
        | Equal (ValueConst (ConstBool true), v) ->
            let str = sprintf "%s" (value_to_string decls v)
            add_parenthesis_if_needed str 10 prec
        | Equal (v, ValueConst (ConstBool false))
        | Equal (ValueConst (ConstBool false), v) ->
            let str = sprintf "~%s" (value_to_string decls v)
            add_parenthesis_if_needed str 5 prec
        // ---------------------------
        | Const b -> sprintf "%b" b
        | Equal (v1, v2) ->
            let str = sprintf "%s = %s" (value_to_string decls v1) (value_to_string decls v2)
            add_parenthesis_if_needed str 4 prec
        | Or (f1,f2) ->
            let str = sprintf "%s | %s" (formula_to_string decls f1 2) (formula_to_string decls f2 2)
            add_parenthesis_if_needed str 2 prec
        | And (f1,f2) ->
            let str = sprintf "%s & %s" (formula_to_string decls f1 3) (formula_to_string decls f2 3)
            add_parenthesis_if_needed str 3 prec
        | Not f ->
            let str = sprintf "~%s" (formula_to_string decls f 5)
            add_parenthesis_if_needed str 5 prec
        | Forall (vd, f) ->
            let decls = Model.add_var_declaration vd decls
            let str = sprintf "F %s. %s" (var_decl_to_string vd) (formula_to_string decls f 1)
            add_parenthesis_if_needed str 1 prec
        | Exists (vd, f) ->
            let decls = Model.add_var_declaration vd decls
            let str = sprintf "E %s. %s" (var_decl_to_string vd) (formula_to_string decls f 1)
            add_parenthesis_if_needed str 1 prec

(*
Precedence:
value : oo (=10)
~ : 5
= : 4
& : 3
| : 2
F E : 1
*)

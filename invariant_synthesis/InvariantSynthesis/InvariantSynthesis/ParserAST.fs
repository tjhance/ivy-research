module ParserAST

open Prime

    (* --- AST TAKEN FROM THE OCAML PARSER --- *)

    (* EXPRESSION *)

    type ivy_type =
        | Unknown
        | Void
        | Bool
        | Uninterpreted of string

    type type_decl = string
    type fun_decl = string * ivy_type list * ivy_type * bool (* Infix? *)
    type var_decl = string * ivy_type

    type const_value =
        | ConstVoid
        | ConstBool of bool
        | ConstInt of string * int

    type parsed_expression =
        | Const of const_value
        | QVar of var_decl
        | VarFunMacroAction of string * parsed_expression list
        | Equal of parsed_expression * parsed_expression
        | Or of parsed_expression * parsed_expression
        | And of parsed_expression * parsed_expression
        | Not of parsed_expression
        | Forall of var_decl * parsed_expression
        | Exists of var_decl * parsed_expression
        | Imply of parsed_expression * parsed_expression
        | SomeElse of var_decl * parsed_expression * parsed_expression option

    (* STATEMENT *)

    type parsed_statement =
        | NewBlock of parsed_statement list
        | NewVar of var_decl * parsed_expression option
        | Expression of parsed_expression
        | VarAssign of string * parsed_expression
        | GeneralFunAssign of string * parsed_expression list * parsed_expression
        | IfElse of parsed_expression * parsed_statement * parsed_statement
        | IfSomeElse of var_decl * parsed_expression * parsed_statement * parsed_statement
        | Assert of parsed_expression
        | Assume of parsed_expression

    (* ELEMENTS *)

    type action_decl = string * var_decl list * var_decl * parsed_statement
    and module_decl = string * string list * parsed_element list

    and parsed_element =
        | Type of type_decl
        | Function of fun_decl
        | Variable of var_decl
        | Macro of string * var_decl list * parsed_expression
        | Definition of string * var_decl list * parsed_expression
        | Conjecture of parsed_expression
        | AbstractAction of string * var_decl list * var_decl
        | Implement of string * parsed_statement
        | Action of action_decl
        | After of string * parsed_statement
        | Before of string * parsed_statement
        | Module of module_decl
        | Object of string * parsed_element list
        | ObjectFromModule of string * string * string list

    (* PARSING AND CONVERSION TOOLS *)

    // Operations on names
    let deserialize str =
        Prime.SymbolicOperators.scvalue<parsed_element list> str

    let separator = '.'

    let local_var_prefix = "$" // We assign a prefix to non-global vars in order to avoid bugs due to vars scope

    let local_name name =
        sprintf "%s%s" local_var_prefix name

    let compose_name base_name name =
        sprintf "%s%c%s" base_name separator name

    let decompose_name (name:string) =
        let i = name.LastIndexOf(separator)
        if i >= 0
        then (Some (name.Substring(0,i)), name.Substring(i+1))
        else (None, name)

    let has_base_name (name:string) (base_name:string) =
        name = base_name || name.StartsWith(sprintf "%s%c" base_name separator)

    let has_reference_name (name:string) reference_name =
        name = reference_name || name.EndsWith(sprintf "%c%s" separator reference_name)

    // Resolve references
    let resolve_reference candidates base_name reference =
        let rec aux base_name =
            let matching_candidates = Set.filter (fun (c:string) -> has_base_name c base_name && has_reference_name c reference) candidates
            if not (Set.isEmpty matching_candidates)
            then
                Helper.seq_min (fun (a:string) (b:string) -> a.Length < b.Length) (Set.toSeq matching_candidates)
            else
                match decompose_name base_name with
                | (None, _) -> failwith ("Can't resolve reference: "+reference)
                | (Some b, _) -> aux b
        aux base_name

    let resolve_reference_all candidates reference =
        List.filter (fun c -> has_reference_name c reference) candidates

    let resolve_type_reference (m:AST.ModuleDecl) base_name reference =
        let candidates = List.map (fun (d:AST.TypeDecl) -> d.Name) m.Types
        resolve_reference (Set.ofList candidates) base_name reference

    // Some helpers
    exception NoMatch
    let types_match expected ret =
        match expected, ret with
        | _, None -> true
        | None, _ -> true
        | Some t1, Some t2 -> Interpreter.type_equal t1 t2

    let conciliate_types t1 t2 =
        match t1, t2 with
        | None, t | t, None -> t
        | t1, t2 ->
            if types_match t1 t2
            then t1 else raise NoMatch

    let conciliate_types3 t1 t2 t3 =
        conciliate_types (conciliate_types t1 t2) t3

    
    // Parsed to AST converters
    let try_p2a_type m base_name ptype =
        match ptype with
        | Unknown -> None
        | Void -> Some AST.Void
        | Bool -> Some AST.Bool
        | Uninterpreted str ->
            let str = resolve_type_reference m base_name str
            Some (AST.Uninterpreted str)

    let p2a_type m base_name ptype =
        match try_p2a_type m base_name ptype with
        | None -> failwith "Unknown type !"
        | Some t -> t

    let p2a_cv pcv t = // Note: parsed ConstInt have always an empty type
        match pcv, t with
        | ConstVoid, Some AST.Void -> AST.ConstVoid
        | ConstBool b, Some AST.Bool -> AST.ConstBool b
        | ConstVoid, None -> AST.ConstVoid
        | ConstBool b, None -> AST.ConstBool b
        | ConstInt _, Some (AST.Uninterpreted str) -> AST.ConstInt (str, 0) // Note: The int constant has no sense without a model, so we put 0.
        | ConstInt _, None -> failwith "Can't guess constant value type!"
        | _, _ -> raise NoMatch

    let p2a_args (m:AST.ModuleDecl) base_name args dico =
        let p2a_arg (str,t) =
            let str = local_name str
            let t = conciliate_types (try_p2a_type m base_name t) (Some (Map.find str dico))
            match t with
            | None -> failwith "Can't infer argument type!"
            | Some t -> { AST.VarDecl.Name=str ; AST.VarDecl.Type=t ; AST.VarDecl.Representation = AST.default_representation }
        List.map p2a_arg args

    // Convert a parsed expression to an AST one, and resolve references & types
    let p2a_expr (m:AST.ModuleDecl) base_name local_vars_types v =

        let rec aux local_vars_types v ret_val =

            let proceed_if_possible lvt rets es =
                if List.length rets <> List.length es then None
                else
                    try
                        let (lvt, res_es) =
                            List.fold2
                                (
                                    fun (lvt, res_es) ret e ->
                                        let (lvt, res_e) = aux lvt e (Some ret)
                                        (lvt, res_e::res_es)
                                ) (lvt,[]) rets es
                        Some (lvt, List.rev res_es)
                    with :? NoMatch -> None

            let proceed_quantifier ((str,t),e) constructor =
                if not (types_match ret_val (Some AST.Bool)) then raise NoMatch
                let str = local_name str
                let old_type = Map.tryFind str local_vars_types
                let local_vars_types = Map.remove str local_vars_types
                let local_vars_types =
                    if t <> Unknown
                    then Map.add str (p2a_type m base_name t) local_vars_types
                    else local_vars_types
                let (local_vars_types, res_e) = aux local_vars_types e (Some AST.Bool)
                let new_type =
                    if Map.containsKey str local_vars_types
                    then Map.find str local_vars_types
                    else AST.Void
                let local_vars_types =
                    match old_type with
                    | None -> Map.remove str local_vars_types
                    | Some t -> Map.add str t local_vars_types
                let decl = { AST.VarDecl.Name=str; AST.VarDecl.Type=new_type; AST.VarDecl.Representation=AST.default_representation}
                (local_vars_types, constructor (decl, AST.expr_to_value res_e))

            let proceed_boolean_operator ts es constructor =
                if not (types_match ret_val (Some AST.Bool)) then raise NoMatch
                match proceed_if_possible local_vars_types ts es with
                    | None -> raise NoMatch
                    | Some (local_vars_types, res_es) -> (local_vars_types, constructor res_es)

            match v with
            | Const cv -> (local_vars_types, AST.ExprConst (p2a_cv cv ret_val))

            | QVar (str, t) ->
                let str = local_name str
                let t = conciliate_types3 (Map.tryFind str local_vars_types) ret_val (try_p2a_type m base_name t)
                match t with
                | None -> failwith "Can't resolve local types: many matches !"
                | Some t -> (Map.add str t local_vars_types, AST.ExprVar str)

            | VarFunMacroAction (str, es) ->

                let candidates_v = Set.map (fun (d:AST.VarDecl) -> (d.Name, [], d.Type, "v")) (Set.ofList m.Vars)
                let candidates_f = Set.map (fun (d:AST.FunDecl) -> (d.Name, d.Input, d.Output, "f")) (Set.ofList m.Funs)
                let candidates_m = Set.map (fun (d:AST.MacroDecl) -> (d.Name, List.map (fun (d:AST.VarDecl) -> d.Type) d.Args, d.Output, "m")) (Set.ofList m.Macros)
                let candidates_a = Set.map (fun (d:AST.ActionDecl) -> (d.Name, List.map (fun (d:AST.VarDecl) -> d.Type) d.Args, d.Output.Type, "a")) (Set.ofList m.Actions)
                let candidates = Set.unionMany [candidates_v;candidates_f;candidates_m;candidates_a]
                let candidates = Set.filter (fun (name,_,_,_) -> has_reference_name name str) candidates
                let candidates = Set.filter (fun (_,_,ret,_) -> types_match ret_val (Some ret)) candidates
                let results = Set.fold (fun acc (str,args,_,descr) -> match proceed_if_possible local_vars_types args es with None -> acc | Some r -> (descr,str,r)::acc) [] candidates

                if List.length results = 1
                then
                    let (descr,str,(local_vars_types, res_es)) = List.head results
                    match descr with
                    | "v" -> (local_vars_types, AST.ExprVar str)
                    | "f" -> (local_vars_types, AST.ExprFun (str,res_es))
                    | "m" -> (local_vars_types, AST.ExprMacro (str,List.map AST.expr_to_value res_es))
                    | "a" -> (local_vars_types, AST.ExprAction (str, res_es))
                    | _ -> failwith "Invalid description."
                else if List.length results = 0
                then raise NoMatch
                else failwith "Can't resolve local types: many matches !"

            | Equal (e1, e2) ->
                if not (types_match ret_val (Some AST.Bool)) then raise NoMatch

                let candidates = List.map (fun (d:AST.TypeDecl) -> AST.Uninterpreted d.Name) m.Types
                let candidates = AST.Void::AST.Bool::candidates
                let results = List.fold (fun acc ret -> match proceed_if_possible local_vars_types [ret;ret] [e1;e2] with None -> acc | Some r -> r::acc) [] candidates

                if List.length results = 1
                then
                    let (local_vars_types, res_es) = List.head results
                    (local_vars_types, AST.ExprEqual (Helper.lst_to_couple res_es))
                else if List.length results = 0
                then raise NoMatch
                else failwith "Can't resolve local types: many matches !"

            | Or (e1, e2) -> proceed_boolean_operator [AST.Bool;AST.Bool] [e1;e2] (fun res_es -> AST.ExprOr (Helper.lst_to_couple res_es))
            | And (e1, e2) -> proceed_boolean_operator [AST.Bool;AST.Bool] [e1;e2] (fun res_es -> AST.ExprAnd (Helper.lst_to_couple res_es))

            | Not e -> proceed_boolean_operator [AST.Bool] [e] (fun res_es -> AST.ExprNot (List.head res_es))

            | Forall ((str,t),e) -> proceed_quantifier ((str,t),e) AST.ExprForall
            | Exists ((str,t),e) -> proceed_quantifier ((str,t),e) AST.ExprExists

            | Imply (e1, e2) -> proceed_boolean_operator [AST.Bool;AST.Bool] [e1;e2] (fun res_es -> AST.ExprImply (Helper.lst_to_couple res_es))

            | SomeElse ((str,t),e1,e2) ->
                let str = local_name str
                let old_type = Map.tryFind str local_vars_types
                let t = conciliate_types (try_p2a_type m base_name t) ret_val
                let local_vars_types =
                    match t with
                    | None -> Map.remove str local_vars_types
                    | Some t -> Map.add str t local_vars_types
                let (local_vars_types, res_e1) = aux local_vars_types e1 (Some AST.Bool)
                let new_type =
                    if Map.containsKey str local_vars_types
                    then Map.find str local_vars_types
                    else AST.Void
                let local_vars_types =
                    match old_type with
                    | None -> Map.remove str local_vars_types
                    | Some t -> Map.add str t local_vars_types
                let decl = { AST.VarDecl.Name=str; AST.VarDecl.Type=new_type; AST.VarDecl.Representation=AST.default_representation}
                let (local_vars_types, res_e2) =
                    match e2 with
                    | Some e2 -> aux local_vars_types e2 (Some new_type)
                    | None -> (local_vars_types, AST.ExprConst (Model.type_default_value new_type))
                (local_vars_types, AST.ExprSomeElse (decl, AST.expr_to_value res_e1, AST.expr_to_value res_e2))

        aux local_vars_types v None
    
    // Add universal quantifiers if needed
    let close_formula local_vars_types args_name f =
        
        let add_quantifier_if_needed acc (name,t) =
            if Set.contains name args_name
            then acc
            else
                let decl = { AST.VarDecl.Name=name; AST.VarDecl.Type=t; AST.VarDecl.Representation=AST.default_representation}
                AST.ExprForall (decl, AST.expr_to_value acc)

        let free_vars = Map.toList local_vars_types
        List.fold add_quantifier_if_needed f free_vars

    // Prepare env dictionnary for the given args
    // Also returns the set of args names
    let env_dictionnary_for (m:AST.ModuleDecl) base_name args =
        let add_arg acc arg =
            match arg with
            | (_, Unknown) -> acc
            | (str, t) ->
                let str = local_name str
                let t = p2a_type m base_name t
                Map.add str t acc
        let dico = List.fold add_arg Map.empty args
        let args_names = List.map (fun (str,_) -> local_name str) args
        (dico, Set.ofList args_names)
    
    // Convert a list of ivy parser AST elements to a global AST.ModuleDecl.
    // Also add and/or adjust references to types, functions, variables or actions of the module.
    let ivy_elements_to_ast_module name elements =
        let rec aux acc base_name elements =
            let treat acc e =
                match e with
                | Type name ->
                    let d = { AST.Name = compose_name base_name name }
                    { acc with AST.Types=(d::acc.Types) }
                | Function (name,args,ret,infix) ->
                    let full_name = compose_name base_name name
                    let args = List.map (p2a_type acc base_name) args
                    let ret = p2a_type acc base_name ret
                    let rep =
                        if infix
                        then { AST.DisplayName=Some name ; AST.Flags=Set.singleton AST.Infix }
                        else AST.default_representation
                    let d = { AST.FunDecl.Name=full_name ; AST.Input=args; AST.Output=ret; AST.Representation=rep }
                    { acc with AST.Funs=(d::acc.Funs) }
                | Variable (name,t) ->
                    let name = compose_name base_name name
                    let t = p2a_type acc base_name t
                    let rep = AST.default_representation
                    let d = { AST.VarDecl.Name=name ; AST.Type=t; AST.VarDecl.Representation=rep }
                    { acc with AST.Vars=(d::acc.Vars) }
                | Macro (name, args, expr) ->
                    let name = compose_name base_name name
                    let (dico, args_names) = env_dictionnary_for acc base_name args
                    let (dico, expr) = p2a_expr acc base_name dico expr
                    let expr = close_formula dico args_names expr
                    let v = AST.expr_to_value expr
                    let args = p2a_args acc base_name args dico
                    let output_t = Interpreter.type_of_value acc v dico
                    let macro = { AST.MacroDecl.Name = name; AST.MacroDecl.Args = args; AST.MacroDecl.Output = output_t; AST.MacroDecl.Value = v }
                    { acc with AST.Macros=(macro::acc.Macros) }

            List.fold treat acc elements
        aux (AST.empty_module name) "" elements



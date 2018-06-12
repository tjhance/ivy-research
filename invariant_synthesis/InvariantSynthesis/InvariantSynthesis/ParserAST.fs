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

    type action_decl = string * var_decl list * var_decl option * parsed_statement
    and module_decl = string * string list * parsed_element list

    and parsed_element =
        | Type of type_decl
        | Function of fun_decl
        | Variable of var_decl
        | Macro of string * var_decl list * parsed_expression
        | Definition of string * var_decl list * parsed_expression
        | Conjecture of parsed_expression
        | AbstractAction of string * var_decl list * var_decl option
        | Implement of string * parsed_statement
        | Action of action_decl
        | After of string * parsed_statement
        | Before of string * parsed_statement
        | Module of module_decl
        | Object of string * parsed_element list
        | ObjectFromModule of string * string * string list

    type parsed_elements = parsed_element list

    (* PARSING AND CONVERSION TOOLS *)

    // Elements rewriting (for parametric modules)
    let rewrite_elements elts dico =

        let exists dico str =
            Map.containsKey str dico

        let test dico str =
            if exists dico str then failwith "Parametric module overrides a parameter !"

        let rewrite dico str =
            match Map.tryFind str dico with
            | None -> str
            | Some str -> str

        let rewrite_t dico t =
            match t with
            | Uninterpreted str -> Uninterpreted (rewrite dico str)
            | Bool -> Bool | Void -> Void | Unknown -> Unknown

        let rewrite_arg_strict dico (str, t) =
            test dico str
            (str, rewrite_t dico t)

        let rewrite_args_strict dico args =
            List.map (rewrite_arg_strict dico) args

        let rewrite_arg dico (str, t) =
            (Map.remove str dico, (str, rewrite_t dico t))

        let rewrite_args dico args =
            let (dico, args) = List.fold (fun (dico,args) arg -> let (dico, arg) = rewrite_arg dico arg in (dico, arg::args) ) (dico,[]) args
            (dico, List.rev args)

        let rewrite_cv dico cv =
            match cv with
            | ConstVoid -> ConstVoid | ConstBool b -> ConstBool b
            | ConstInt (str,i) -> ConstInt (rewrite dico str,i)

        let rec rewrite_expr dico expr =
            match expr with
            | Const cv -> Const (rewrite_cv dico cv) | QVar d -> QVar d
            | VarFunMacroAction (str, exprs) -> VarFunMacroAction (rewrite dico str, List.map (rewrite_expr dico) exprs)
            | Equal (expr1, expr2) -> Equal (rewrite_expr dico expr1, rewrite_expr dico expr2)
            | Or (expr1, expr2) -> Or (rewrite_expr dico expr1, rewrite_expr dico expr2)
            | And (expr1, expr2) -> And (rewrite_expr dico expr1, rewrite_expr dico expr2)
            | Not expr -> Not (rewrite_expr dico expr)
            | Forall (d, expr) -> let (_, d) = rewrite_arg dico d in Forall (d, rewrite_expr dico expr)
            | Exists (d, expr) -> let (_, d) = rewrite_arg dico d in Forall (d, rewrite_expr dico expr)
            | Imply (expr1, expr2) -> Imply (rewrite_expr dico expr1, rewrite_expr dico expr2)
            | SomeElse (d, expr, expr_opt) -> let (_, d) = rewrite_arg dico d in SomeElse (d, rewrite_expr dico expr, Option.map (rewrite_expr dico) expr_opt)

        let rec rewrite_stat dico s =
            let sts = rewrite_stats dico [s]
            if List.length sts <> 1 then failwith "Internal error."
            else List.head sts
        and rewrite_stats dico sts =
            match sts with
            | [] -> []
            | (NewBlock sts1)::sts -> (NewBlock (rewrite_stats dico sts1))::(rewrite_stats dico sts)
            | (NewVar (d, expr_opt))::sts ->
                let expr_opt = Option.map (rewrite_expr dico) expr_opt
                let (dico, d) = rewrite_arg dico d
                (NewVar (d, expr_opt))::(rewrite_stats dico sts)
            | (Expression e)::sts -> (Expression (rewrite_expr dico e))::(rewrite_stats dico sts)
            | (VarAssign (str, expr))::sts -> (VarAssign (rewrite dico str, rewrite_expr dico expr))::(rewrite_stats dico sts)
            | (GeneralFunAssign (str, exprs, expr))::sts ->
                (GeneralFunAssign (rewrite dico str, List.map (rewrite_expr dico) exprs , rewrite_expr dico expr))::(rewrite_stats dico sts)
            | (IfElse (expr, st1, st2))::sts -> (IfElse (rewrite_expr dico expr, rewrite_stat dico st1, rewrite_stat dico st2))::(rewrite_stats dico sts)
            | (IfSomeElse (d, expr, st1, st2))::sts ->
                let (dico', d) = rewrite_arg dico d
                (IfSomeElse (d, rewrite_expr dico' expr, rewrite_stat dico' st1, rewrite_stat dico st2))::(rewrite_stats dico sts)
            | (Assert expr)::sts -> (Assert (rewrite_expr dico expr))::(rewrite_stats dico sts)
            | (Assume expr)::sts -> (Assume (rewrite_expr dico expr))::(rewrite_stats dico sts)

        let rec rewrite_element dico elt =
            match elt with
            | Type str -> test dico str ; Type str
            | Function (str, args, ret_t, b) ->
                test dico str
                Function (str, List.map (rewrite_t dico) args, rewrite_t dico ret_t, b)
            | Variable (str, t) ->
                test dico str
                Variable (str, rewrite_t dico t)
            | Macro (str, args, expr) ->
                test dico str
                let (dico, args) = rewrite_args dico args
                Macro (str, args, rewrite_expr dico expr)
            | Definition (str, args, expr) ->
                let str = rewrite dico str
                let (dico, args) = rewrite_args dico args
                Definition (str, args, rewrite_expr dico expr)
            | Conjecture expr -> Conjecture (rewrite_expr dico expr)
            | AbstractAction (str, args, ret_opt) ->
                test dico str
                let args = rewrite_args_strict dico args
                let ret_opt = Option.map (rewrite_arg_strict dico) ret_opt
                AbstractAction (str, args, ret_opt)
            | Implement (str, st) -> test dico str ; Implement (str, rewrite_stat dico st)
            | Action (str, args, ret_opt, st) ->
                test dico str
                let args = rewrite_args_strict dico args
                let ret_opt = Option.map (rewrite_arg_strict dico) ret_opt
                Action (str, args, ret_opt, rewrite_stat dico st)
            | After (str, st) -> test dico str ; After (str, rewrite_stat dico st)
            | Before (str, st) -> test dico str ; Before (str, rewrite_stat dico st)
            | Module (str, args, elts) ->
                test dico str
                let dico = List.fold (fun acc arg -> Map.remove arg acc) dico args
                Module (str, args, List.map (rewrite_element dico) elts)
            | Object (str, elts) -> test dico str ; Object (str, List.map (rewrite_element dico) elts)
            | ObjectFromModule (str, module_name, args) ->
                test dico str
                ObjectFromModule (str, rewrite dico module_name, List.map (rewrite dico) args)

        List.map (rewrite_element dico) elts

    // Operations on names
    let deserialize str =
        Prime.SymbolicOperators.scvalue<parsed_element list> str

    let separator = '.'

    let name_variant_char = ':'

    let local_var_prefix = "$" // We assign a prefix to non-global vars in order to avoid bugs due to vars scope

    let impossible_var_name = "$$"

    let void_return_decl = AST.default_var_decl impossible_var_name AST.Void

    let local_name name =
        sprintf "%s%s" local_var_prefix name

    let variant_name name variant =
        if variant = ""
        then name
        else sprintf "%s%c%s" name name_variant_char variant

    let compose_name base_name name =
        if name = ""
        then base_name
        else if base_name = ""
        then name
        else sprintf "%s%c%s" base_name separator name

    // Decompose a name and returns a tuple of the form (parent_name,last_name)
    let decompose_name (name:string) =
        let i = name.LastIndexOf(separator)
        if i >= 0
        then (name.Substring(0,i), name.Substring(i+1))
        else ("", name)

    let has_base_name (name:string) (base_name:string) =
        base_name = "" || name = base_name || name.StartsWith(sprintf "%s%c" base_name separator)

    let has_reference_name (name:string) reference_name =
        name = reference_name || name.EndsWith(sprintf "%c%s" separator reference_name)

    // Resolve references
    let resolve_reference candidates base_name reference =
        let rec aux base_name =
            let matching_candidates = Set.filter (fun (c:string) -> has_base_name c base_name && has_reference_name c reference) candidates
            if not (Set.isEmpty matching_candidates)
            then
                Helper.seq_min (fun (a:string) (b:string) -> a.Length < b.Length) (Set.toSeq matching_candidates)
            else if base_name = ""
            then failwith ("Can't resolve reference: "+reference)
            else
                let (b, _) = decompose_name base_name
                aux b
        aux base_name

    let resolve_reference_all candidates reference =
        Set.filter (fun c -> has_reference_name c reference) candidates

    let resolve_type_reference (m:AST.ModuleDecl) base_name reference =
        let candidates = List.map (fun (d:AST.TypeDecl) -> d.Name) m.Types
        resolve_reference (Set.ofList candidates) base_name reference

    // Some helpers
    exception NoMatch of string
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
            then t1 else raise (NoMatch (sprintf "Types %A and %A don't match!" t1 t2))

    let conciliate_types3 t1 t2 t3 =
        conciliate_types (conciliate_types t1 t2) t3

    let all_types (m:AST.ModuleDecl) =
        let res = List.map (fun (d:AST.TypeDecl) -> AST.Uninterpreted d.Name) m.Types
        AST.Void::AST.Bool::res

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
        | _, _ -> raise (NoMatch (sprintf "Const value %A don't match the type %A!" pcv t))

    let p2a_decl (m:AST.ModuleDecl) base_name (str,t) dico =
        let str = local_name str
        let t = conciliate_types (try_p2a_type m base_name t) (Map.tryFind str dico)
        match t with
        | None -> failwith "Can't infer argument type!"
        | Some t -> AST.default_var_decl str t

    let p2a_args (m:AST.ModuleDecl) base_name args dico =
        List.map (fun arg -> p2a_decl m base_name arg dico) args

    // Convert a parsed expression to an AST one, and resolve references & types
    let p2a_expr (m:AST.ModuleDecl) base_name st_local_vars local_vars_types ret_val v =

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
                if not (types_match ret_val (Some AST.Bool)) then raise (NoMatch "Can't quantify a non-boolean value.")
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
                let decl = AST.default_var_decl str new_type
                (local_vars_types, constructor (decl, AST.expr_to_value res_e))

            let proceed_operator ret_type ts es constructor =
                if not (types_match ret_val (Some ret_type)) then raise (NoMatch "Operator has wrong return type!")
                match proceed_if_possible local_vars_types ts es with
                    | None -> raise (NoMatch "Operator applied to wrong args type!")
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
                // If a st_local_var match, priority to it!
                if List.length es = 0 && Map.containsKey (local_name str) st_local_vars
                then
                    let str = local_name str
                    if not (types_match ret_val (Some (Map.find str st_local_vars))) then raise (NoMatch (sprintf "Local var %s has wrong return type!" str))
                    (local_vars_types, AST.ExprVar str)
                else
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
                    then raise (NoMatch (sprintf "Can't find any var/fun/macro/action %s that match the required return and args types!" str))
                    else failwith "Can't resolve local types: many matches !"

            | Equal (e1, e2) ->
                if not (types_match ret_val (Some AST.Bool)) then raise (NoMatch "Equal operator should have boolean return type!")

                let candidates = all_types m
                let results = List.fold (fun acc ret -> match proceed_if_possible local_vars_types [ret;ret] [e1;e2] with None -> acc | Some r -> r::acc) [] candidates

                if List.length results = 1
                then
                    let (local_vars_types, res_es) = List.head results
                    (local_vars_types, AST.ExprEqual (Helper.lst_to_couple res_es))
                else if List.length results = 0
                then raise (NoMatch "Can't test equality on args of diffrent types!")
                else failwith "Can't resolve local types: many matches !"

            | Or (e1, e2) -> proceed_operator AST.Bool [AST.Bool;AST.Bool] [e1;e2] (fun res_es -> AST.ExprOr (Helper.lst_to_couple res_es))
            | And (e1, e2) -> proceed_operator AST.Bool [AST.Bool;AST.Bool] [e1;e2] (fun res_es -> AST.ExprAnd (Helper.lst_to_couple res_es))

            | Not e -> proceed_operator AST.Bool [AST.Bool] [e] (fun res_es -> AST.ExprNot (List.head res_es))

            | Forall ((str,t),e) -> proceed_quantifier ((str,t),e) AST.ExprForall
            | Exists ((str,t),e) -> proceed_quantifier ((str,t),e) AST.ExprExists

            | Imply (e1, e2) -> proceed_operator AST.Bool [AST.Bool;AST.Bool] [e1;e2] (fun res_es -> AST.ExprImply (Helper.lst_to_couple res_es))

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
                let decl = AST.default_var_decl str new_type
                let (local_vars_types, res_e2) =
                    match e2 with
                    | Some e2 -> aux local_vars_types e2 (Some new_type)
                    | None -> (local_vars_types, AST.ExprConst (Model.type_default_value new_type))
                (local_vars_types, AST.ExprSomeElse (decl, AST.expr_to_value res_e1, AST.expr_to_value res_e2))

        aux local_vars_types v ret_val

    // Add universal quantifiers if needed
    let close_formula (m:AST.ModuleDecl) local_vars_types args_name f =
        
        let add_quantifier_if_needed acc (name,t) =
            if Set.contains name args_name
            then acc
            else
                if Interpreter.type_of_expr m acc local_vars_types <> AST.Bool then failwith "Can't close the value because it is not a formula!"
                else
                    let decl = AST.default_var_decl name t
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

    // Convert a parsed statement to an AST one, and resolve references & types
    let p2a_stats (m:AST.ModuleDecl) base_name sts local_vars =
        let rec aux sts local_vars =
            match sts with
            | [] -> []
            | (NewBlock sts1)::sts2 -> (aux sts1 local_vars)@(aux sts2 local_vars)
            | (NewVar ((str,t), e_opt))::sts ->
                // decl & e
                let compute_formula t e =
                    let (dico, e) = p2a_expr m base_name local_vars Map.empty (try_p2a_type m base_name t) e
                    close_formula m dico Set.empty e
                let str = local_name str
                let e_opt = Option.map (compute_formula t) e_opt
                let t = conciliate_types (try_p2a_type m base_name t) (Option.map (fun e ->Interpreter.type_of_expr m e Map.empty) e_opt)
                let t =
                    match t with
                    | None -> failwith "Can't infer type of new var !"
                    | Some t -> t
                let d = AST.default_var_decl str t
                // sts
                let sts = aux sts (Map.add d.Name d.Type local_vars)
                let sts =
                    match e_opt with
                    | None -> sts
                    | Some e -> (AST.VarAssign (d.Name, e))::sts
                [AST.NewBlock ([d], sts)]

            | (Expression e)::sts ->
                let (dico, e) = p2a_expr m base_name local_vars Map.empty None e
                let e = close_formula m dico Set.empty e
                (AST.Expression e)::(aux sts local_vars)

            | (VarAssign (str,e))::sts ->
                let (str,t) = // Resolve reference. Priority to local vars.
                    if Map.containsKey (local_name str) local_vars
                    then (local_name str, Map.find (local_name str) local_vars)
                    else
                        let candidates = List.map (fun (d:AST.VarDecl) -> d.Name) m.Vars
                        (resolve_reference (Set.ofList candidates) base_name str, (AST.find_variable m str).Type)
                let (dico, e) = p2a_expr m base_name local_vars Map.empty (Some t) e
                let e = close_formula m dico Set.empty e
                (AST.VarAssign (str, e))::(aux sts local_vars)

            | (GeneralFunAssign (str,es,e))::sts ->
                let candidates = List.filter (fun (f:AST.FunDecl) -> List.length f.Input = List.length es) m.Funs
                let candidates = List.map (fun (f:AST.FunDecl) -> f.Name) candidates
                let str = resolve_reference (Set.ofList candidates) base_name str
                let fun_def = AST.find_function m str

                let qvar_of e t =
                    match e with
                    | QVar (str, t') ->
                        let t = match conciliate_types (Some t) (try_p2a_type m base_name t') with None -> failwith "Internal error." | Some t -> t
                        Some (local_name str, t)
                    | _ -> None
                let free_vars = Helper.option_lst_to_lst (List.map2 qvar_of es fun_def.Input)
                if List.length free_vars > 0
                then
                    // v
                    let dico = List.fold (fun acc (str,t) -> Map.add str t acc) Map.empty free_vars
                    let args_name = List.map (fun (str,_) -> str) free_vars
                    let (dico, e) = p2a_expr m base_name local_vars dico (Some fun_def.Output) e
                    let e = close_formula m dico (Set.ofList args_name) e
                    let v = AST.expr_to_value e
                    // hes
                    let treat_he e t =
                        match e with
                        | QVar (str,_) ->
                            let str = local_name str
                            AST.Hole (AST.default_var_decl str t)
                        | e ->
                            let (dico, e) = p2a_expr m base_name local_vars Map.empty (Some t) e
                            let e = close_formula m dico Set.empty e
                            AST.Expr e
                    let hes = List.map2 treat_he es fun_def.Input
                    (AST.ForallFunAssign (str, hes, v))::(aux sts local_vars)
                else
                    let es = List.map2 (fun e t -> p2a_expr m base_name local_vars Map.empty (Some t) e) es fun_def.Input
                    let es = List.map (fun (dico, e) -> close_formula m dico Set.empty e) es
                    let (dico, e) = p2a_expr m base_name local_vars Map.empty (Some fun_def.Output) e
                    let e = close_formula m dico Set.empty e
                    (AST.FunAssign (str, es, e))::(aux sts local_vars)

            | (IfElse (e, sif, selse))::sts ->
                let (dico, e) = p2a_expr m base_name local_vars Map.empty (Some AST.Bool) e
                let e = close_formula m dico Set.empty e
                let sif = aux [sif] local_vars
                let selse = aux [selse] local_vars
                (AST.IfElse (e,AST.NewBlock([],sif),AST.NewBlock([],selse)))::(aux sts local_vars)

            | (IfSomeElse ((str,t),e,sif,selse))::sts ->
                // decl & v
                let str = local_name str
                let local_vars_e_candidates =
                    match try_p2a_type m base_name t with
                    | Some t -> [Map.add str t local_vars]
                    | None -> List.map (fun t -> Map.add str t local_vars) (all_types m)

                let add_if_possible acc local_vars_e =
                    try
                        let (dico, e) = p2a_expr m base_name local_vars_e Map.empty (Some AST.Bool) e
                        (dico,e,local_vars_e)::acc
                    with :? NoMatch -> acc
                let results =
                    List.fold add_if_possible [] local_vars_e_candidates

                let (dico,e,local_vars_e) =
                    if List.length results = 1
                    then List.head results
                    else if List.length results > 1
                    then failwith "Can't resolve 'if some' local type: too many matches !"
                    else raise (NoMatch (sprintf "No match for 'if some' local type %s!" str))

                let e = close_formula m dico Set.empty e
                let v = AST.expr_to_value e
                let t = Map.find str local_vars_e
                // sif & selse
                let sif = aux [sif] local_vars_e
                let selse = aux [selse] local_vars
                (AST.IfSomeElse (AST.default_var_decl str t, v, AST.NewBlock([],sif),AST.NewBlock([],selse)))::(aux sts local_vars)

            | (Assert e)::sts ->
                let (dico, e) = p2a_expr m base_name local_vars Map.empty (Some AST.Bool) e
                let e = close_formula m dico Set.empty e
                let v = AST.expr_to_value e
                (AST.Assert v)::(aux sts local_vars)

            | (Assume _)::sts ->
                printfn "Assume ignored."
                aux sts local_vars

        aux sts local_vars
    
    type template_elements = { AbstractActions: Map<string, List<AST.VarDecl> * AST.VarDecl> ; Modules: Map<string * int, List<string> * List<parsed_element>> }
    let empty_template_elements = { AbstractActions = Map.empty ; Modules = Map.empty }

    // Convert a list of ivy parser AST elements to a global AST.ModuleDecl.
    // Also add and/or adjust references to types, functions, variables or actions of the module.
    let ivy_elements_to_ast_module name elements =
        let rec aux m tmp_elements base_name elements =

            let implement_action (m,tmp_elements) (name, st) variant =
                let candidates = List.map (fun (n,_) -> n) (Map.toList tmp_elements.AbstractActions)
                let name = resolve_reference (Set.ofList candidates) base_name name
                let (args, ret) = Map.find name tmp_elements.AbstractActions
                let local_vars = List.fold (fun acc (v:AST.VarDecl) -> Map.add v.Name v.Type acc) Map.empty (ret::args)
                let st = p2a_stats m base_name [st] local_vars
                let action = { AST.ActionDecl.Name = variant_name name variant; AST.ActionDecl.Args = args ; AST.ActionDecl.Output = ret ; AST.ActionDecl.Content = AST.NewBlock([],st) }
                ({ m with AST.Actions=(action::m.Actions) }, tmp_elements)

            let rec treat (m,tmp_elements) e =
                match e with
                | Type name ->
                    let d = { AST.Name = compose_name base_name name }
                    ({ m with AST.Types=(d::m.Types) }, tmp_elements)
                | Function (name,args,ret,infix) ->
                    let full_name = compose_name base_name name
                    let args = List.map (p2a_type m base_name) args
                    let ret = p2a_type m base_name ret
                    let rep =
                        if infix
                        then { AST.DisplayName=Some name ; AST.Flags=Set.singleton AST.Infix }
                        else AST.default_representation
                    let d = { AST.FunDecl.Name=full_name ; AST.Input=args; AST.Output=ret; AST.Representation=rep }
                    ({ m with AST.Funs=(d::m.Funs) }, tmp_elements)
                | Variable (name,t) ->
                    let name = compose_name base_name name
                    let t = p2a_type m base_name t
                    let d = AST.default_var_decl name t
                    ({ m with AST.Vars=(d::m.Vars) }, tmp_elements)
                | Macro (name, args, expr) ->
                    let name = compose_name base_name name
                    let (dico, args_names) = env_dictionnary_for m base_name args
                    let (dico, expr) = p2a_expr m base_name Map.empty dico None expr
                    let expr = close_formula m dico args_names expr
                    let v = AST.expr_to_value expr
                    let args = p2a_args m base_name args dico
                    let output_t = Interpreter.type_of_value m v dico
                    let macro = { AST.MacroDecl.Name = name; AST.MacroDecl.Args = args; AST.MacroDecl.Output = output_t; AST.MacroDecl.Value = v }
                    ({ m with AST.Macros=(macro::m.Macros) }, tmp_elements)
                | Definition _ ->
                    printfn "Definition ignored."
                    (m, tmp_elements)
                | Conjecture expr ->
                    let (dico, expr) = p2a_expr m base_name Map.empty Map.empty (Some AST.Bool) expr
                    let expr = close_formula m dico Set.empty expr
                    let v = AST.expr_to_value expr
                    ({ m with AST.Invariants=(v::m.Invariants) }, tmp_elements)
                | AbstractAction (name, args, ret_opt) ->
                    let name = compose_name base_name name
                    let args = p2a_args m base_name args Map.empty
                    let ret =
                        match ret_opt with
                        | None -> void_return_decl
                        | Some (str,t) -> p2a_decl m base_name (str,t) Map.empty
                    (m, { tmp_elements with AbstractActions = (Map.add name (args,ret) tmp_elements.AbstractActions) })
                | Implement (name, st) ->
                    implement_action (m,tmp_elements) (name,st) ""
                | Action (name, args, ret_opt, st) ->
                    let (m, tmp_elements) = treat (m, tmp_elements) (AbstractAction (name, args, ret_opt))
                    treat (m, tmp_elements) (Implement (name, st))
                | Before (name, st) ->
                    implement_action (m,tmp_elements) (name,st) "before"
                | After (name, st) ->
                    implement_action (m,tmp_elements) (name,st) "after"
                | Module (name, args, elts) ->
                    let name = compose_name base_name name
                    (m, { tmp_elements with Modules=(Map.add (name, List.length args) (args, elts) tmp_elements.Modules) })
                | Object (name, elts) ->
                    let name = compose_name base_name name
                    aux m tmp_elements name elts
                | ObjectFromModule (name, module_name, args) ->
                    let name = compose_name base_name name
                    let candidates_t = Set.ofList (List.map (fun (t:AST.TypeDecl) -> t.Name) m.Types)
                    let candidates_v = Set.ofList (List.map (fun (v:AST.VarDecl) -> v.Name) m.Vars)
                    let candidates_f = Set.ofList (List.map (fun (f:AST.FunDecl) -> f.Name) m.Funs)
                    let candidates_ma = Set.ofList (List.map (fun (m:AST.MacroDecl) -> m.Name) m.Macros)
                    let candidates_a = Set.ofList (List.map (fun (a:AST.ActionDecl) -> a.Name) m.Actions)
                    let candidates_mo = Set.ofList (List.map (fun ((str,_),_) -> str) (Map.toList tmp_elements.Modules))
                    let resolve_arg_if_possible arg =
                        let candidates = Set.unionMany [candidates_t;candidates_v;candidates_f;candidates_ma;candidates_a;candidates_mo]
                        match Set.toList (resolve_reference_all candidates arg) with
                        | [arg] -> arg
                        | _ -> arg
                    let args = List.map resolve_arg_if_possible args
                    let candidates_mo = Set.filter (fun n -> Map.containsKey (n,List.length args) tmp_elements.Modules) candidates_mo
                    let module_name = resolve_reference candidates_mo base_name module_name

                    let (prev_args, elts) = Map.find (module_name,List.length args) tmp_elements.Modules
                    let dico = List.fold2 (fun acc p n -> Map.add p n acc) Map.empty prev_args args
                    let elts = rewrite_elements elts dico
                    aux m tmp_elements name elts

            List.fold treat (m,tmp_elements) elements
        let (m,_) = aux (AST.empty_module name) empty_template_elements "" elements
        m

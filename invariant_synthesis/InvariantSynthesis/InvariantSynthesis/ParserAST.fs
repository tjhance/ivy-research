module ParserAST

    (* --- AST TAKEN FROM THE OCAML PARSER --- *)

    (* EXPRESSION *)

    type ivy_type =
        | Void
        | Bool
        | Uninterpreted of string

    type type_decl = string
    type fun_decl = string * ivy_type list * ivy_type * bool (* Infix? *)
    type var_decl = string * ivy_type

    type const_value =
        | ConstVoid
        | ConstBool of bool
        | ConstInt of int

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
        | SomeElse of var_decl * parsed_expression * parsed_expression

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

    let deserialize str =
        Prime.SymbolicOperators.scvalue<parsed_element list> str

    let separator = '.'

    let local_var_prefix = "$" // We assign a prefix to non-global vars in order to avoid bugs due to vars scope

    let compose_name base_name name =
        sprintf "%s%c%s" base_name separator name

    let decompose_name (name:string) =
        let i = name.LastIndexOf(separator)
        if i >= 0
        then (Some (name.Substring(0,i)), name.Substring(i+1))
        else (None, name)

    // Resolve references
    let resolve_reference candidates base_name reference =
        let rec aux base_name =
            let name = compose_name base_name reference
            if Set.contains name candidates
            then name
            else
                match decompose_name base_name with
                | (None, _) -> failwith ("Can't resolve reference: "+reference)
                | (Some b, _) -> aux b
        aux base_name

    let resolve_type_reference (m:AST.ModuleDecl) base_name reference =
        let candidates = List.map (fun (d:AST.TypeDecl) -> d.Name) m.Types
        resolve_reference (Set.ofList candidates) base_name reference
    
    // Parsing to AST converters
    let p2a_type m base_name ptype =
        match ptype with
        | Void -> AST.Void
        | Bool -> AST.Bool
        | Uninterpreted str ->
            let str = resolve_type_reference m base_name str
            AST.Uninterpreted str
    
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

            List.fold treat acc elements
        aux (AST.empty_module name) "" elements



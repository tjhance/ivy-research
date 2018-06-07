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
        | VarFunAction of string * parsed_expression list
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

    let deserialize str =
        Prime.SymbolicOperators.scvalue<parsed_element list> str

    let separator = '.'

    let compose_name base_name name =
        sprintf "%s%c%s" base_name separator name

    let decompose_name (name:string) =
        let i = name.LastIndexOf(separator)
        if i >= 0
        then (Some (name.Substring(0,i)), name.Substring(i+1))
        else (None, name)

    let resolve_reference base_name reference candidates =
        let rec aux base_name =
            let name = compose_name base_name reference
            if Set.contains name candidates
            then name
            else
                match decompose_name base_name with
                | (None, _) -> failwith ("Can't resolve reference: "+reference)
                | (Some b, _) -> aux b
        aux base_name

    let resolve_type_reference base_name reference (m:AST.ModuleDecl) =
        let candidates = List.map (fun (d:AST.TypeDecl) -> d.Name) m.Types
        resolve_reference base_name reference (Set.ofList candidates)
    
    // Parsing to AST converters
    let p2a_type ptype = ()
        
    // Convert a list of ivy parser AST elements to a global AST.ModuleDecl.
    // Also add and/or adjust references to types, functions, variables or actions of the module.
    let ivy_elements_to_ast_module name elements =
        let rec aux acc base_name elements =
            let treat acc e =
                match e with
                | Type name ->
                    let name = { AST.Name = compose_name base_name name }
                    { acc with AST.Types=(name::acc.Types) }
                //| Function (name,args,ret,infix) ->

            List.fold treat acc elements
        aux (AST.empty_module name) "" elements



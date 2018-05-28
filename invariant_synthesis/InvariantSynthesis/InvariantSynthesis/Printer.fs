module Printer

    open AST

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
                    then sprintf "(%s %s %s)" (aux (List.head vs)) str (aux (List.head (List.tail vs)))
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
            add_parenthesis_if_needed str 5 prec
        | Equal (v, ValueConst (ConstBool true))
        | Equal (ValueConst (ConstBool true), v) ->
            let str = sprintf "%s" (value_to_string decls v)
            add_parenthesis_if_needed str 10 prec
        | Equal (v, ValueConst (ConstBool false))
        | Equal (ValueConst (ConstBool false), v) ->
            let str = sprintf "~%s" (value_to_string decls v)
            add_parenthesis_if_needed str 6 prec
        // ---------------------------
        | Const b -> sprintf "%b" b
        | Equal (v1, v2) ->
            let str = sprintf "%s = %s" (value_to_string decls v1) (value_to_string decls v2)
            add_parenthesis_if_needed str 5 prec
        | Or (f1,f2) ->
            let str = sprintf "%s | %s" (formula_to_string decls f1 3) (formula_to_string decls f2 3)
            add_parenthesis_if_needed str 3 prec
        | And (f1,f2) ->
            let str = sprintf "%s & %s" (formula_to_string decls f1 4) (formula_to_string decls f2 4)
            add_parenthesis_if_needed str 4 prec
        | Not f ->
            let str = sprintf "~%s" (formula_to_string decls f 6)
            add_parenthesis_if_needed str 6 prec
        | Forall (vd, f) ->
            let decls = Model.add_var_declaration vd decls
            let str = sprintf "F %s. %s" (var_decl_to_string vd) (formula_to_string decls f 1)
            add_parenthesis_if_needed str 1 prec
        | Exists (vd, f) ->
            let decls = Model.add_var_declaration vd decls
            let str = sprintf "E %s. %s" (var_decl_to_string vd) (formula_to_string decls f 1)
            add_parenthesis_if_needed str 1 prec
        | Imply (f1,f2) ->
            let str = sprintf "%s -> %s" (formula_to_string decls f1 2) (formula_to_string decls f2 2)
            add_parenthesis_if_needed str 2 prec

    (*
    Precedence:
    value : oo (=10)
    ~ : 6
    = : 5
    & : 4
    | : 3
    -> : 2
    F E : 1
    *)

    let varmark_to_string decls (env:Model.Environment) str =
        let value = Map.find str env.v
        let formula = Equal (ValueVar str, ValueConst value)
        formula_to_string decls formula 0

    let funmark_to_string decls (env:Model.Environment) (str, cvs) =
        let value = Map.find (str, cvs) env.f
        let cvs = List.map (fun cv -> ValueConst cv) cvs
        let formula = Equal (ValueFun (str, cvs), ValueConst value)
        formula_to_string decls formula 0

    let marks_to_string decls (env:Model.Environment) (m:Synthesis.Marks) =
        let res = Set.fold (fun acc v -> sprintf "%s%s\n" acc (varmark_to_string decls env v)) "" m.v
        let res = Set.fold (fun acc f -> sprintf "%s%s\n" acc (funmark_to_string decls env f)) res m.f
        res

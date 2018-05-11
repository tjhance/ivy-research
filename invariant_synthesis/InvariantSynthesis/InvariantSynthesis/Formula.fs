module Formula

    open AST

    let formula_from_marks (env:Model.Environment) (m:Synthesis.Marks) =
        Const true // TODO

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
        | Forall (vd, f) -> sprintf "∀%s.%s" (var_decl_to_string vd) (formula_to_string f)
        | Exists (vd, f) -> sprintf "∃%s.%s" (var_decl_to_string vd) (formula_to_string f)

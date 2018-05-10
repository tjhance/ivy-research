module ConstraintsParser
    
    open FParsec
    open AST

    type UserState = unit
    type Parser<'t> = Parser<'t, UserState>

    type ModuleDecl = ModuleDecl<Model.TypeInfos, Model.Environment>

    let identifier : Parser<string> =
        let isIdentifierFirstChar c = isLetter c || c = '_'
        let isIdentifierChar c = isLetter c || isDigit c || c = '_' || c = '.'
        many1Satisfy2 isIdentifierFirstChar isIdentifierChar

    let infix_special : Parser<List<char>> =
        many (anyOf ['<'; '='; '>'; '~'])

    let nl  : Parser<unit> = (newline |>> ignore) <|> eof

    let find_relation (m:ModuleDecl) str =
        List.find (fun (decl:FunDecl) -> decl.Name = str) m.Funs

    let string_of_type t =
        match t with
        | Uninterpreted str -> str
        | _ -> failwith "Wrong arg type!"

    ///////////////////////////////////////////////////////////////////////

    let parse_var_constraints_uninterpreted =
        pipe3
            (pint32 .>> pstring ":")
            (identifier .>> spaces .>> pstring "=" .>> spaces)
            (identifier .>> nl)
            (fun v t i -> [Model.Variable(i,ConstInt (t, v))])

    let parse_var_constraints_unused : Parser<List<Model.Constraint>> =
        pipe3
            (pint32 .>> pstring ":")
            (identifier .>> spaces .>> pstring "~=" .>> spaces)
            (identifier .>> nl)
            (fun _ _ _ -> [])

    let parse_var_constraints_bool_true =
        identifier .>> nl
        |>> (fun i -> [Model.Variable(i,ConstBool true)])

    let parse_var_constraints_bool_false =
        pstring "~" >>. identifier .>> nl
        |>> (fun i -> [Model.Variable(i,ConstBool false)])

    let parse_var_constraints =
        parse_var_constraints_uninterpreted
        <|> parse_var_constraints_bool_true
        <|> parse_var_constraints_bool_false
        <|> parse_var_constraints_unused

    ///////////////////////////////////////////////////////////////////////

    let parse_fun_constraints_uninterpreted (m:ModuleDecl) =
        pipe4
            (identifier .>> pstring "(")
            (pint32)
            (many (pstring "," >>. spaces >>. pint32))
            (pstring ")" >>. spaces >>. pstring "=" >>. spaces >>. pint32 .>> nl)
            (fun i h l v ->
                let rel = find_relation m i
                let args = List.map2 (fun t v -> ConstInt(string_of_type t, v)) rel.Input (h::l)
                let output = ConstInt(string_of_type rel.Output, v)
                [Model.Function(i,args,output)]
            )

    let parse_fun_constraints_unused : Parser<List<Model.Constraint>> =
        pipe4
            (identifier .>> pstring "(")
            (pint32)
            (many (pstring "," >>. spaces >>. pint32))
            (pstring ")" >>. spaces >>. pstring "~=" >>. spaces >>. pint32 .>> nl)
            (fun _ _ _ _ -> [])

    let parse_fun_constraints_bool_true (m:ModuleDecl) =
        pipe3
            (identifier .>> pstring "(")
            (pint32)
            (many (pstring "," >>. spaces >>. pint32) .>> pstring ")" .>> nl)
            (fun i h l ->
                let rel = find_relation m i
                let args = List.map2 (fun t v -> ConstInt(string_of_type t, v)) rel.Input (h::l)
                [Model.Function(i,args,ConstBool true)]
            )

    let parse_fun_constraints_bool_false (m:ModuleDecl) =
        pipe3
            (pstring "~" >>. identifier .>> pstring "(")
            (pint32)
            (many (pstring "," >>. spaces >>. pint32) .>> pstring ")" .>> nl)
            (fun i h l ->
                let rel = find_relation m i
                let args = List.map2 (fun t v -> ConstInt(string_of_type t, v)) rel.Input (h::l)
                [Model.Function(i,args,ConstBool false)]
            )

    let parse_fun_constraints (m:ModuleDecl) =
        parse_fun_constraints_uninterpreted m
        <|> parse_fun_constraints_bool_true m
        <|> parse_fun_constraints_bool_false m
        <|> parse_fun_constraints_unused

    ///////////////////////////////////////////////////////////////////////

    let parse_constraints_infix_special =
        pipe4
            (pint32 .>> pstring ":")
            (identifier .>> spaces)
            (infix_special .>> spaces)
            (pint32 .>> nl)
            (fun v1 t op v2 ->
                match op with
                | ['='] | ['~';'='] ->
                    [Model.Bound(t,v1);Model.Bound(t,v2)]
                | ['<'] ->
                    [Model.Function (t + ".<", [ConstInt(t,v1);ConstInt(t,v2)], ConstBool true)]
                | _ -> failwith "Undefined infix operator"
            )

    ///////////////////////////////////////////////////////////////////////

    let parse_constraints (m:ModuleDecl) =
        many (parse_var_constraints <|> parse_fun_constraints m <|> parse_constraints_infix_special)
        |>> List.concat

module ConstraintsParser
    
    open FParsec
    open AST

    type UserState = unit
    type Parser<'t> = Parser<'t, UserState>

    let identifier : Parser<string> =
        let isIdentifierFirstChar c = isLetter c || c = '_'
        let isIdentifierChar c = isLetter c || isDigit c || c = '_' || c = '.'
        many1Satisfy2 isIdentifierFirstChar isIdentifierChar

    let infix_special : Parser<List<char>> =
        many (anyOf ['<'; '='; '>'; '~'])

    let nl  : Parser<unit> = (newline |>> ignore) <|> eof

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
        attempt parse_var_constraints_uninterpreted
        <|> attempt parse_var_constraints_bool_true
        <|> attempt parse_var_constraints_bool_false
        <|> attempt parse_var_constraints_unused

    ///////////////////////////////////////////////////////////////////////

    let parse_fun_constraints_uninterpreted (m:ModuleDecl) =
        pipe4
            (identifier .>> pstring "(")
            (pint32)
            (many (pstring "," >>. spaces >>. pint32))
            (pstring ")" >>. spaces >>. pstring "=" >>. spaces >>. pint32 .>> nl)
            (fun i h l v ->
                let rel = find_function m i
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
                let rel = find_function m i
                let args = List.map2 (fun t v -> ConstInt(string_of_type t, v)) rel.Input (h::l)
                [Model.Function(i,args,ConstBool true)]
            )

    let parse_fun_constraints_bool_false (m:ModuleDecl) =
        pipe3
            (pstring "~" >>. identifier .>> pstring "(")
            (pint32)
            (many (pstring "," >>. spaces >>. pint32) .>> pstring ")" .>> nl)
            (fun i h l ->
                let rel = find_function m i
                let args = List.map2 (fun t v -> ConstInt(string_of_type t, v)) rel.Input (h::l)
                [Model.Function(i,args,ConstBool false)]
            )

    let parse_fun_constraints (m:ModuleDecl) =
        attempt (parse_fun_constraints_uninterpreted m)
        <|> attempt (parse_fun_constraints_bool_true m)
        <|> attempt (parse_fun_constraints_bool_false m)
        <|> attempt parse_fun_constraints_unused

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
        many
            (
                attempt parse_var_constraints
                <|> attempt (parse_fun_constraints m)
                <|> attempt parse_constraints_infix_special
            )
        |>> List.concat

    let parse_from_str (m:ModuleDecl) str =
        match runParserOnString (parse_constraints m) () "Input String" str with
        | Failure (err,_,_) -> failwith err
        | Success (res,_,_) -> res

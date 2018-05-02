module Interpreter

    open AST

    let rec evaluate_value (env:Model.Environment) v =
        match v with
        | ValueConst cv -> cv
        | ValueVar str -> Map.find str env.v
        | ValueFun (str, lst) ->
            let lst = List.map (evaluate_value env) lst
            Map.find (str, lst) env.f

    let rec evaluate_formula (env:Model.Environment) f =
        match f with
        | Const b -> b
        | Equal (v1,v2) ->
            let v1 = evaluate_value env v1
            let v2 = evaluate_value env v2
            v1 = v2
        | Or (f1,f2) ->
            let f1 = evaluate_formula env f1
            let f2 = evaluate_formula env f2
            f1 || f2
        | And (f1,f2) ->
            let f1 = evaluate_formula env f1
            let f2 = evaluate_formula env f2
            f1 && f2
        | Not f -> not (evaluate_formula env f)
        | _ -> false // TODO

    let evaluate_expression (env:Model.Environment) e = ()
    let evaluate_statement (env:Model.Environment) s = ()

    let execute (env:Model.Environment) statement = ()
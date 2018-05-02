module Interpreter

    open AST
    open System.Collections.Generic

    let all_values (env:Model.Environment) data_type =
        match data_type with
        | Void -> Seq.singleton ConstVoid
        | Bool -> [ConstBool false; ConstBool true] |> Seq.ofList
        | Custom s ->
            let max = Map.find s env.b
            seq { for x in 0..max -> ConstInt (s, x) }

    let rec evaluate_value (env:Model.Environment) v =
        match v with
        | ValueConst cv -> cv
        | ValueVar str -> Map.find str env.v
        | ValueFun (str, lst) ->
            let lst = List.map (evaluate_value env) lst
            Map.find (str, lst) env.f
    
    // Two values are equal iff they are structuraly equal or are explicitely declared equal.
    let value_equal (env:Model.Environment) v1 v2 =
        if v1=v2 then true
        else
            try
                Map.find (v1,v2) env.e
            with :? KeyNotFoundException ->
                try
                    Map.find (v2,v1) env.e
                with :? KeyNotFoundException -> false

    let rec evaluate_formula (env:Model.Environment) f =
        match f with
        | Const b -> b
        | Equal (v1,v2) ->
            let v1 = evaluate_value env v1
            let v2 = evaluate_value env v2
            value_equal env v1 v2
        | Or (f1,f2) ->
            let f1 = evaluate_formula env f1
            let f2 = evaluate_formula env f2
            f1 || f2
        | And (f1,f2) ->
            let f1 = evaluate_formula env f1
            let f2 = evaluate_formula env f2
            f1 && f2
        | Not f -> not (evaluate_formula env f)
        | Forall (d,f) ->
            let eval_with value =
                let v' = Map.add d.Name value env.v
                evaluate_formula { env with v=v' } f
            let possible_values = all_values env d.Type
            Seq.forall eval_with possible_values
        | Exists (d,f) ->
            let eval_with value =
                let v' = Map.add d.Name value env.v
                evaluate_formula { env with v=v' } f
            let possible_values = all_values env d.Type
            Seq.exists eval_with possible_values
    
    let value_or v1 v2 =
        match v1, v2 with
        | ConstBool b1, ConstBool b2 -> ConstBool (b1 || b2)
        | _ -> ConstVoid

    let value_and v1 v2 =
        match v1, v2 with
        | ConstBool b1, ConstBool b2 -> ConstBool (b1 && b2)
        | _ -> ConstVoid

    let value_not v =
        match v with
        | ConstBool b -> ConstBool (not b)
        | _ -> ConstVoid

    let rec evaluate_expression (m:ModuleDecl) (env:Model.Environment) e =
        match e with
        | ExprConst cv -> (env, cv)
        | ExprVar v -> (env, evaluate_value env (ValueVar v))
        | ExprFun (str, lst) ->
            let (env, lst) = evaluate_expressions m env lst
            let lst = List.map (fun cv -> ValueConst cv) lst
            (env, evaluate_value env (ValueFun (str, lst)))
        | ExprAction (str, lst) ->
            let (env, lst) = evaluate_expressions m env lst
            execute_action m env str lst
        | ExprEqual (e1, e2) ->
            let (env, v1) = evaluate_expression m env e1
            let (env, v2) = evaluate_expression m env e2
            (env, ConstBool (value_equal env v1 v2))
        | ExprOr (e1, e2) -> 
            let (env, v1) = evaluate_expression m env e1
            let (env, v2) = evaluate_expression m env e2
            (env, value_or v1 v2)
        | ExprAnd (e1, e2) -> 
            let (env, v1) = evaluate_expression m env e1
            let (env, v2) = evaluate_expression m env e2
            (env, value_and v1 v2)
        | ExprNot e -> 
            let (env, v) = evaluate_expression m env e
            (env, value_not v)

    and evaluate_expressions (m:ModuleDecl) (env:Model.Environment) es =
        let aux (env, res) e =
            let (env, v) = evaluate_expression m env e
            (env, v::res)
        let (env, res) = List.fold aux (env, []) es
        (env, List.rev res)

    and execute_statement (m:ModuleDecl) (env:Model.Environment) s =
        () // TODO

    and execute_action (m:ModuleDecl) (env:Model.Environment) action args =
        (env, ConstVoid) // TODO

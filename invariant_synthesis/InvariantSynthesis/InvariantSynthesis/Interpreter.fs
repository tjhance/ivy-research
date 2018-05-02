module Interpreter

    open AST

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

    let rec evaluate_expression (m:ModuleDecl) (env:Model.Environment) e = ()

    and execute_statement (m:ModuleDecl) (env:Model.Environment) s = ()

    and execute_action (m:ModuleDecl) (env:Model.Environment) action args = ()

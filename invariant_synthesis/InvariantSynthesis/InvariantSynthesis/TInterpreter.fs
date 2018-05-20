module TInterpreter

    open AST
    open Trace

    exception ExprAssertionFailed of TrExpression * Formula
    exception StAssertionFailed of TrStatement * Formula

    let rec trace_expression (m:ModuleDecl) infos (env:Model.Environment) e =
        match e with
        | ExprConst cv ->
            let red = (env,env,Some cv)
            TrExprConst (red, cv)

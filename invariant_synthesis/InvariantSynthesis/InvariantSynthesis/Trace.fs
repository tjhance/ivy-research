module Trace

    open AST
    open Model
    open System.Drawing

    type RuntimeStData = Environment * Environment
    type RuntimeExprData = Environment * Environment * ConstValue option

    type TrExpression =
        | TrExprConst of RuntimeExprData * ConstValue
        | TrExprVar of RuntimeExprData * string
        | TrExprFun of RuntimeExprData * string * List<TrExpression>
        | TrExprAction of RuntimeExprData * List<VarDecl> * VarDecl * List<TrExpression> * TrStatement
        | TrExprAbstract of RuntimeExprData
        | TrExprEqual of RuntimeExprData * TrExpression * TrExpression
        | TrExprOr of RuntimeExprData * TrExpression * TrExpression
        | TrExprAnd of RuntimeExprData * TrExpression * TrExpression
        | TrExprNot of RuntimeExprData * TrExpression
        | TrExprSomeElse of RuntimeExprData * VarDecl * Formula * Value
        | TrExprNotEvaluated

    and TrHoleExpression =
        | TrHole of VarDecl
        | TrExpr of TrExpression

    and TrStatement =
        | TrNewBlock of RuntimeStData * List<VarDecl> * List<TrStatement>
        | TrExpression of RuntimeStData * TrExpression
        | TrVarAssign of RuntimeStData * string * TrExpression
        | TrFunAssign of RuntimeStData * string * List<TrExpression> * TrExpression
        | TrForallFunAssign of RuntimeStData * string * List<TrHoleExpression> * Value
        | TrIfElse of RuntimeStData * TrExpression * TrStatement
        | TrIfSomeElse of RuntimeStData * Option<ConstValue> * VarDecl * Formula * TrStatement
        | TrAssert of RuntimeStData * Formula
        | TrNotEvaluated

    let runtime_data_of_expr expr =
        match expr with
        | TrExprConst (red,_)
        | TrExprVar (red,_)
        | TrExprFun (red,_,_)
        | TrExprAction (red,_,_,_,_)
        | TrExprAbstract red
        | TrExprEqual (red,_,_)
        | TrExprOr (red,_,_)
        | TrExprAnd (red,_,_)
        | TrExprNot (red,_)
        | TrExprSomeElse (red,_,_,_) -> Some red
        | TrExprNotEvaluated -> None

    let expr_is_fully_evaluated expr =
        match runtime_data_of_expr expr with
        | None -> false
        | Some (_,_,None) -> false
        | Some (_,_,Some _) -> true

    let exprs_are_fully_evaluated exprs =
        List.forall expr_is_fully_evaluated exprs

    exception NoRuntimeData
    exception NotFullyEvaluated

    let final_env_of_expr expr =
        match runtime_data_of_expr expr with
        | None -> raise NoRuntimeData
        | Some (_,env,_) -> env

    let final_env_of_exprs exprs initial_env =
        let aux acc e =
            try
                final_env_of_expr e
            with :? NoRuntimeData -> acc
        List.fold aux initial_env exprs

    let initial_env_of_expr expr =
        match runtime_data_of_expr expr with
        | None -> raise NoRuntimeData
        | Some (env,_,_) -> env

    let ret_value_of_expr expr =
        match runtime_data_of_expr expr with
        | None -> raise NoRuntimeData
        | Some (_,_,None) -> raise NotFullyEvaluated
        | Some (_,_,Some ret) -> ret
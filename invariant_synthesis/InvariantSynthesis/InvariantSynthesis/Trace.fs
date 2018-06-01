module Trace

    open AST
    open Model
    open System.Drawing

    type RuntimeStData = Environment * Environment * bool
    type RuntimeExprData = Environment * Environment * ConstValue option

    type TrExpression =
        | TrExprConst of RuntimeExprData * ConstValue
        | TrExprVar of RuntimeExprData * string
        | TrExprFun of RuntimeExprData * string * List<TrExpression>
        | TrExprAction of RuntimeExprData * List<VarDecl> * VarDecl * List<TrExpression> * TrStatement
        | TrExprEqual of RuntimeExprData * TrExpression * TrExpression
        | TrExprOr of RuntimeExprData * TrExpression * TrExpression
        | TrExprAnd of RuntimeExprData * TrExpression * TrExpression
        | TrExprNot of RuntimeExprData * TrExpression
        | TrExprSomeElse of RuntimeExprData * Option<ConstValue> * VarDecl * Formula * Value
        | TrExprNotEvaluated of RuntimeExprData

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
        | TrNotEvaluated of RuntimeStData

    let runtime_data_of_expr expr =
        match expr with
        | TrExprConst (red,_)
        | TrExprVar (red,_)
        | TrExprFun (red,_,_)
        | TrExprAction (red,_,_,_,_)
        | TrExprEqual (red,_,_)
        | TrExprOr (red,_,_)
        | TrExprAnd (red,_,_)
        | TrExprNot (red,_)
        | TrExprSomeElse (red,_,_,_,_)
        | TrExprNotEvaluated red -> red

    let runtime_data_of_st s =
        match s with
        | TrNewBlock (red,_,_)
        | TrExpression (red,_)
        | TrVarAssign (red,_,_)
        | TrFunAssign (red,_,_,_)
        | TrForallFunAssign (red,_,_,_)
        | TrIfElse (red,_,_)
        | TrIfSomeElse (red,_,_,_,_)
        | TrAssert (red,_)
        | TrNotEvaluated red -> red

    let st_is_fully_executed s =
        let (_,_,b) = runtime_data_of_st s
        b

    let expr_is_fully_evaluated expr =
        let (_,_,v) = runtime_data_of_expr expr
        v <> None

    let exprs_are_fully_evaluated exprs =
        List.forall expr_is_fully_evaluated exprs

    let sts_are_fully_executed sts =
        List.forall st_is_fully_executed sts

    let final_env_of_expr expr =
        let (_,env,_) = runtime_data_of_expr expr
        env

    let final_env_of_st st =
        let (_,env,_) = runtime_data_of_st st
        env

    let final_env_of_exprs exprs initial_env =
        let aux _ e =
            final_env_of_expr e
        List.fold aux initial_env exprs

    let final_env_of_sts sts initial_env =
        let aux _ s =
            final_env_of_st s
        List.fold aux initial_env sts

    let initial_env_of_expr expr =
        let (env,_,_) = runtime_data_of_expr expr
        env

    let initial_env_of_st st =
        let (env,_,_) = runtime_data_of_st st
        env

    exception NotFullyEvaluated
    let ret_value_of_expr expr =
        match runtime_data_of_expr expr with
        | (_,_,None) -> raise NotFullyEvaluated
        | (_,_,Some ret) -> ret
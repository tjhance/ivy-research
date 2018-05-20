module Trace

    open AST
    open Model

    type RuntimeStData = Environment * Environment
    type RuntimeExprData = Environment * Environment * ConstValue option

    type TrExpression =
        | TrExprConst of RuntimeExprData * ConstValue
        | TrExprVar of RuntimeExprData * string
        | TrExprFun of RuntimeExprData * List<TrExpression>
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

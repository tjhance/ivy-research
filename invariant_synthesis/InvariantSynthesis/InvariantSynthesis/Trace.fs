module Trace

    open MinimalAST
    open Model

    type RuntimeData = Environment * Environment * bool // Env before, env after, successfully executed

    type TrStatement =
        | TrNewBlock of RuntimeData * List<VarDecl> * List<TrStatement>
        | TrVarAssign of RuntimeData * string * Value
        | TrVarAssignAction of
            RuntimeData * Option<ConstValue> * string * List<VarDecl> * VarDecl * List<Value> * TrStatement
        | TrFunAssign of RuntimeData * string * List<HoleValue> * Value
        | TrIfElse of RuntimeData * Value * TrStatement
        | TrIfSomeElse of RuntimeData * Option<ConstValue> * VarDecl * Value * TrStatement
        | TrAssert of RuntimeData * Value

    let runtime_data s =
        match s with
        | TrNewBlock (rd,_,_)
        | TrVarAssign (rd,_,_)
        | TrVarAssignAction (rd,_,_,_,_,_,_)
        | TrFunAssign (rd,_,_,_)
        | TrIfElse (rd,_,_)
        | TrIfSomeElse (rd,_,_,_,_)
        | TrAssert (rd,_) -> rd

    let is_fully_executed st =
        let (_,_,b) = runtime_data st
        b

    let are_fully_executed sts =
        List.forall is_fully_executed sts

    let final_env st =
        let (_,env,_) = runtime_data st
        env

    let final_env_of_sts sts initial_env =
        let aux _ s =
            final_env s
        List.fold aux initial_env sts

    let initial_env st =
        let (env,_,_) = runtime_data st
        env
    
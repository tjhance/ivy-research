module WPR

    open MinimalAST

    type Statement =
        | NewBlock of List<VarDecl> * List<Statement>
        | VarAssign of string * Value
        | VarAssignAction of string * string * List<Value>
        | FunAssign of string * List<VarDecl> * Value
        | Parallel of Statement * Statement
        | Assume of Value
        | Abort



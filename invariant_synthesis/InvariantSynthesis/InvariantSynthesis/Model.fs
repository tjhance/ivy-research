namespace Model

    (* TYPES TO DESCRIBE (FINITE) MODELS AND ENVIRONMENTS *)
    open AST

    type BoundConstraint = string * int // For custom types, the number of elements - 1
    type FunConstraint = string * List<ConstValue> * ConstValue
    type VarConstraint = string * ConstValue

    type Constraint =
        | Bound of BoundConstraint
        | Function of FunConstraint
        | Variable of VarConstraint

    type Model = { b : List<BoundConstraint> ; f : List<FunConstraint>; v : List<VarConstraint> }
    type Model' = List<Constraint>

    type BoundEnv = Map<string, int>
    type FunEnv = Map<string * List<ConstValue>, ConstValue>
    type VarEnv = Map<string, ConstValue>

    type Environment = { b : BoundEnv; f : FunEnv; v : VarEnv }



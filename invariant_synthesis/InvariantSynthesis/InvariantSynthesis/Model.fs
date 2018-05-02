namespace Model

    (* TYPES TO DESCRIBE (FINITE) MODELS AND ENVIRONMENTS *)
    open AST

    type BoundConstraint = string * int // For custom types, the number of elements - 1
    type EqConstraint = ConstValue * ConstValue * bool
    type FunConstraint = string * List<ConstValue> * ConstValue
    type VarConstraint = string * ConstValue

    type Constraint =
        | Bound of BoundConstraint
        | Equality of EqConstraint
        | Function of FunConstraint
        | Variable of VarConstraint

    type Model = { b : List<BoundConstraint> ; e : List<EqConstraint>; f : List<FunConstraint>; v : List<VarConstraint> }
    type Model' = List<Constraint>

    type BoundEnv = Map<string, int>
    type EqEnv = Map<ConstValue * ConstValue, bool>
    type FunEnv = Map<string * List<ConstValue>, ConstValue>
    type VarEnv = Map<string, ConstValue>

    type Environment = { b : BoundEnv; s : EqEnv; f : FunEnv; v : VarEnv }



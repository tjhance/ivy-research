namespace Model

    (* TYPES TO DESCRIBE (FINITE) MODELS AND ENVIRONMENTS *)
    open AST

    type BoundConstraint = string * int // For custom types, the number of elements - 1
    // EqConstraints are used by the synthesis tool to divide a type into multiple isomorphic instances.
    // If two values of different type are equal, a constraint MUST exists. Should be symetric.
    // There should be no constraint when values have the same type.
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

    type Environment = { b : BoundEnv; e : EqEnv; f : FunEnv; v : VarEnv }



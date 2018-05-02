namespace IVY

    (* TYPES TO DESCRIBE (FINITE) MODELS AND ENVIRONMENTS *)

    type Value = IVY.Type * IVY.ConstValue // Type, uninterpreted runtime value

    type StructualOperator = Eq | Diff //| SSmaller // '<' can be considered as a regular relation
    type StructConstraint = Value * StructualOperator * Value
    type FunConstraint = string * List<Value> * Value
    type VarConstraint = string * Value

    type Constraint =
        | Structural of StructConstraint
        | Function of FunConstraint
        | Variable of VarConstraint

    type Model = { s : List<StructConstraint>; f : List<FunConstraint>; v : List<VarConstraint> }
    type Model' = List<Constraint>

    type StructEnv = Map<Value * Value, StructualOperator>
    type FunEnv = Map<string * List<Value>, Value>
    type VarEnv = Map<string, Value>

    type Environment = { s : StructEnv; f : FunEnv; v : VarEnv }



namespace IVY

    (* TYPES TO DESCRIBE (FINITE) MODELS AND ENVIRONMENTS *)

    type value = string * int // Type, uninterpreted runtime value

    type StructualOperator = Eq | Diff //| SSmaller // '<' can be considered as a regular relation
    type StructuralConstraint = value * StructualOperator * value
    type RelationConstraint = string * List<value> * bool
    type FunctionConstraint = string * List<value> * value
    type VariableConstraint = string * value

    type Constraint =
        | Structural of StructuralConstraint
        | Relation of RelationConstraint
        | Function of FunctionConstraint
        | Variable of VariableConstraint

    type Model = List<Constraint>
    type Model' = { s : List<StructuralConstraint>; r : List<RelationConstraint>; f : List<FunctionConstraint>; v : List<VariableConstraint> }

    type RelationEnv = Map<string * List<value>, bool>
    type FunctionEnv = Map<string * List<value>, value>
    type VariableEnv = Map<string, value>

    type Environment = { s : List<StructuralConstraint>; r : RelationEnv; f : FunctionEnv; v : VariableEnv }



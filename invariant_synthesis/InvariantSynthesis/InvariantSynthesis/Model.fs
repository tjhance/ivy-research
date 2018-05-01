namespace Model

(* TYPES TO DESCRIBE (FINITE) MODELS *)

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

type Model = { s : StructuralConstraint; r : RelationConstraint; f : FunctionConstraint; v : VariableConstraint }


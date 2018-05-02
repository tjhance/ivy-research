namespace IVY

    module Synthesis =

        type StructMark = Set<Value * Value>
        type FunMark = Set<string * List<Value>>
        type VarMark = Set<string>

        type Marks = { s: StructMark; f: FunMark; v: VarMark }

        let mark_constraints_for_formula env cs f = ()

        let update_marks env cs st = ()


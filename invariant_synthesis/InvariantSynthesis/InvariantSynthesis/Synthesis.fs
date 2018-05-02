module Synthesis

    open AST

    type EqMarks = Set<ConstValue * ConstValue>
    type FunMarks = Set<string * List<ConstValue>>
    type VarMarks = Set<string>

    type Marks = { s: EqMarks; f: FunMarks; v: VarMarks }

    let mark_constraints_for_formula env cs f = ()

    let update_marks env cs st = ()


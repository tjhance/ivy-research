module Synthesis

    open AST
    open Interpreter

    type FunMarks = Set<string * List<ConstValue>>
    type VarMarks = Set<string>
    type DiffMarks = Set<ConstValue * ConstValue>

    type Marks = { f : FunMarks; v : VarMarks; d : DiffMarks }

    let empty_marks = { f = Set.empty; v = Set.empty ; d = Set.empty }

    let marks_union m1 m2 =
        { f = Set.union m1.f m2.f ; v = Set.union m1.v m2.v ; d = Set.union m1.d m2.d }
    
    let marks_union_many ms =
        let fs = Seq.map (fun m -> m.f) ms
        let vs = Seq.map (fun m -> m.v) ms
        let ds = Seq.map (fun m -> m.d) ms
        { f = Set.unionMany fs ; v = Set.unionMany vs ; d = Set.unionMany ds }

    let rec marks_for_value infos env v : ConstValue * Marks =
        match v with
        | ValueConst c -> (c, empty_marks)
        | ValueVar str -> (evaluate_value env (ValueVar str), { empty_marks with v=Set.singleton str })
        | ValueFun (str, values) ->
            let res = List.map (marks_for_value infos env) values
            let (cvs, ms) = List.unzip res
            let m = marks_union_many ms
            let vs = List.map (fun cv -> ValueConst cv) cvs
            (evaluate_value env (ValueFun (str, vs)), { m with f = Set.add (str, cvs) m.f })

    let rec marks_for_formula infos env f : bool * Marks =
        match f with
        | Const  b -> (b, empty_marks)
        | Equal (v1, v2) ->
            let (cv1, m1) = marks_for_value infos env v1
            let (cv2, m2) = marks_for_value infos env v2
            let m = marks_union m1 m2
            if value_equal infos cv1 cv2 then (true, m)
            else
                let d' =
                    if Set.contains (cv1, cv2) m.d || Set.contains (cv2, cv1) m.d
                    then m.d else Set.add (cv1, cv2) m.d
                (false, { m with d = d' })
        | Or (f1, f2) ->
            let (b1, m1) = marks_for_formula infos env f1
            let (b2, m2) = marks_for_formula infos env f2
            match b1, b2 with
            | false, false -> (false, marks_union m1 m2)
            | true, false -> (true, m1)
            | false, true -> (true, m2)
            | true, true -> (true, m1) // We arbitrary choose m1 !
        | And (f1, f2) ->
            let (b1, m1) = marks_for_formula infos env f1
            let (b2, m2) = marks_for_formula infos env f2
            match b1, b2 with
            | false, false -> (false, m1) // We arbitrary choose m1 !
            | true, false -> (false, m2)
            | false, true -> (false, m1)
            | true, true -> (true, marks_union m1 m2)
        | Not f ->
            let (b,m) = marks_for_formula infos env f
            (not b, m)
        // TODO

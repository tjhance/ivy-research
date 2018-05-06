module Synthesis

    open AST
    open Interpreter
    open System.Data.SqlTypes

    type FunMarks = Set<string * List<ConstValue>>
    type VarMarks = Set<string>
    type DiffMarks = Set<ConstValue * ConstValue>

    type Marks = { f : FunMarks; v : VarMarks; d : DiffMarks }

    let empty_marks = { f = Set.empty; v = Set.empty ; d = Set.empty }

    let marks_count m =
        (Set.count m.f) + (Set.count m.v) + (Set.count m.d)

    let marks_map op1 op2 op3 ms : Marks =
        let fs = Seq.map (fun m -> m.f) ms
        let vs = Seq.map (fun m -> m.v) ms
        let ds = Seq.map (fun m -> m.d) ms
        { f = op1 fs ; v = op2 vs ; d = op3 ds }
    
    let marks_union_many = marks_map Set.unionMany Set.unionMany Set.unionMany    
    let marks_inter_many = marks_map Set.intersectMany Set.intersectMany Set.intersectMany
    let marks_union m1 m2 = marks_union_many ([m1;m2] |> List.toSeq)
    let marks_inter m1 m2 = marks_inter_many ([m1;m2] |> List.toSeq)
    let marks_diff m1 m2 =
        { f = Set.difference m1.f m2.f ; v = Set.difference m1.v m2.v ; d = Set.difference m1.d m2.d }

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

    // Return type : (formula value, important elements, universally quantified important elements)
    let rec marks_for_formula infos env f : bool * Marks * Marks =
        match f with
        | Const  b -> (b, empty_marks, empty_marks)
        | Equal (v1, v2) ->
            let (cv1, m1) = marks_for_value infos env v1
            let (cv2, m2) = marks_for_value infos env v2
            let m = marks_union m1 m2
            if value_equal infos cv1 cv2 then (true, m, empty_marks)
            else
                let d' =
                    if Set.contains (cv1, cv2) m.d || Set.contains (cv2, cv1) m.d
                    then m.d else Set.add (cv1, cv2) m.d
                (false, { m with d = d' }, empty_marks)
        | Or (f1, f2) ->
            let (b1, m1, um1) = marks_for_formula infos env f1
            let (b2, m2, um2) = marks_for_formula infos env f2
            match b1, b2 with
            | false, false -> (false, marks_union m1 m2, marks_union um1 um2)
            | true, false -> (true, m1, um1)
            | false, true -> (true, m2, um2)
            | true, true when marks_count um1 > marks_count um2 -> (true, m2, um2)
            | true, true -> (true, m1, um1)
        | And (f1, f2) ->
            marks_for_formula infos env (Not (Or (Not f1, Not f2)))
        | Not f ->
            let (b,m,um) = marks_for_formula infos env f
            (not b, m, um)
        | Forall (decl, f) ->
            let marks_with value =
                let v' = Map.add decl.Name value env.v
                let (b, m, um) = marks_for_formula infos { env with v=v' } f
                let m = { m with v = Set.remove decl.Name m.v }
                let um = { um with v = Set.remove decl.Name um.v }
                (b, m, um)
            let values = all_values infos decl.Type
            let all_possibilities = Seq.map marks_with values
            if Seq.forall (fun (b,_,_) -> b) all_possibilities
            then
                // Important constraints are universally quantified...
                // Common properties stay in m, other properties move to um
                let ms = Seq.map (fun (_,m,_) -> m) all_possibilities
                let ums = Seq.map (fun (_,_,um) -> um) all_possibilities
                let m = marks_inter_many ms
                let um1 = marks_union_many ums
                let um2 = marks_diff (marks_union_many ms) m
                (true, m, marks_union um1 um2)
            else
                // We pick one constraint that breaks the forall
                let min_count (mb, mm, mum) (b, m, um) = if marks_count um < marks_count mm then (b, m, um) else (mb, mm, mum)
                let interesting_possibilities = Seq.filter (fun (b, _, _) -> not b) all_possibilities
                let (_, m, um) = Seq.fold min_count (Seq.head interesting_possibilities) interesting_possibilities
                (false, m, um)
        | Exists (decl, f) ->
            marks_for_formula infos env (Not (Forall (decl, Not f)))

    // env: initial environment (before the execution of the expressions)
    // Returns the final environment
    // Returns the list of each environment before the execution of an expression, IN THE REVERSE ORDER
    // Also returns the values of the expressions (in the initial order
    let intermediate_environments module_decl infos env es =
        let aux (envs, vs) e =
            let (h, v) = evaluate_expression module_decl infos (List.head envs) e
            (h::envs, v::vs)
        let (envs, vs) = (List.fold aux ([env], []) es)
        (List.head envs, List.tail envs, List.rev vs)

    let intermediate_environments_st module_decl infos env sts =
        let aux envs st =
            let h = execute_statement module_decl infos (List.head envs) st
            (h::envs)
        let envs = (List.fold aux [env] sts)
        (List.head envs, List.tail envs)

    let marks_leave_block infos m lvars old_m : Marks =
        let rollback acc (decl:VarDecl) =
            if Set.contains decl.Name old_m.v
            then Set.add decl.Name acc
            else Set.remove decl.Name acc
        { m with v=List.fold rollback m.v lvars }

    let marks_enter_block infos m lvars : Marks =
        let rm acc (decl:VarDecl) = Set.remove decl.Name acc
        { m with v=List.fold rm m.v lvars }

    let is_var_marked infos m um (var_decl:VarDecl) =
        (Set.contains var_decl.Name m.v) || (Set.contains var_decl.Name um.v)

    // env: initial environment (before the execution of the expr)
    // m, um: marks after the execution of the expr
    // Return type : (important elements, universally quantified important elements)
    let rec marks_before_expression module_decl infos env expr m um mark_value =
        match expr with
        | ExprConst _ -> (m, um)
        | ExprVar str ->
            let (_, m') = marks_for_value infos env (ValueVar str)
            let m = if mark_value then marks_union m m' else m
            (m, um)
        | ExprFun (str, es) ->
            let (env, envs, vs) = intermediate_environments module_decl infos env es
            let (_, m') = marks_for_value infos env (ValueFun (str, List.map (fun v -> ValueConst v) vs))
            let m =
                if mark_value
                then marks_union m m'
                else m
            marks_before_expressions module_decl infos envs (List.rev es) m um (List.map (fun _ -> mark_value) es)
        | ExprAction (str, es) ->
            let (env, envs, lst) = intermediate_environments module_decl infos env es
            let (args_marks, m, um) = marks_before_action module_decl infos env str lst m um mark_value
            marks_before_expressions module_decl infos envs (List.rev es) m um args_marks
        // TODO

    // envs: the env before each expression
    and marks_before_expressions module_decl infos envs es m um mark_values =
        let aux (m, um) (env, e) mark =
            marks_before_expression module_decl infos env e m um mark
        let (m, um) = List.fold2 aux (m, um) (List.zip envs es) mark_values
        (m, um)

    and marks_before_statement module_decl infos env st m um = (m, um) // TODO

    and marks_before_action (mdecl:ModuleDecl) infos env action args m um mark_value =
        let action_decl = List.find (fun (adecl:ActionDecl) -> adecl.Name = action) mdecl.Actions
        let env' = enter_new_block infos env (action_decl.Output::action_decl.Args) (None::(List.map (fun a -> Some a) args))
        let m' = marks_enter_block infos m (action_decl.Output::action_decl.Args)
        let um' = marks_enter_block infos um (action_decl.Output::action_decl.Args)
        let m' =
            if mark_value then
                { m' with v = Set.add action_decl.Output.Name m'.v }
            else m'
        let (m', um') = marks_before_statement mdecl infos env' action_decl.Content m' um'
        let args_marks = List.map (is_var_marked infos m' um') action_decl.Args
        let m' = marks_leave_block infos m' (action_decl.Output::action_decl.Args) m
        let um' = marks_leave_block infos um' (action_decl.Output::action_decl.Args) um
        (args_marks, m', um')
        // TODO: Handle abstract actions
module Solver

    let z3_formula_for_constraints (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) (m:Marking.Marks) =
        let add_var_constraint cs str = // Constraints on the arguments
            let cv = Map.find str env.v
            AST.ValueAnd (cs, AST.ValueEqual (AST.ValueVar str, AST.ValueConst cv))
        let cs = Set.fold add_var_constraint (AST.ValueConst (AST.ConstBool true)) m.v
        let add_fun_constraint cs (str, cvs) =
            let cv = Map.find (str, cvs) env.f
            let vs = List.map (fun cv -> AST.ValueConst cv) cvs
            AST.ValueAnd (cs, AST.ValueEqual (AST.ValueFun (str, vs), AST.ValueConst cv))
        let cs = Set.fold add_fun_constraint cs m.f
        let add_diff_constraint cs (cv1, cv2) =
            AST.ValueAnd (cs, AST.ValueNot (AST.ValueEqual (AST.ValueConst cv1, AST.ValueConst cv2)))
        let cs = Set.fold add_diff_constraint cs m.d
        let cs = MinimalAST.value2minimal md cs
        WPR.z3val2deterministic_formula (WPR.minimal_val2z3_val mmd cs) false

    let z3_formula_for_axioms_and_conjectures (mmd:MinimalAST.ModuleDecl<'a,'b>) =
        let all_invariants = MinimalAST.invariants_to_formulas mmd.Invariants
        let conjectures = WPR.conjunction_of (WPR.conjectures_to_z3values mmd all_invariants)
        let axioms = WPR.conjunction_of (WPR.conjectures_to_z3values mmd mmd.Axioms)
        WPR.Z3And (axioms, conjectures)

    let z3_formula_for_wpr (mmd:MinimalAST.ModuleDecl<'a,'b>) action formula uq_args =
        let z3formula = WPR.z3val2deterministic_formula (WPR.minimal_val2z3_val mmd formula) false
        WPR.wpr_for_action mmd z3formula action uq_args

    let check_z3_formula (mmd:MinimalAST.ModuleDecl<'a,'b>) action f timeout =
        let z3ctx = Z3Utils.build_context mmd
        let args_decl =
            match action with
            | None -> []
            | Some action -> (MinimalAST.find_action mmd action).Args
        let (z3lvars, z3concrete_map) = Z3Utils.declare_lvars args_decl z3ctx f
        let z3e = Z3Utils.build_value z3ctx z3lvars f
        match Z3Utils.check z3ctx z3e timeout with
        | None -> None
        | Some m -> Some (Z3Utils.z3model_to_ast_model mmd z3ctx args_decl z3lvars z3concrete_map m)

    let check_z3_formula_ext (mmd:MinimalAST.ModuleDecl<'a,'b>) action f timeout =
        let z3ctx = Z3Utils.build_context mmd
        let args_decl =
            match action with
            | None -> []
            | Some action -> (MinimalAST.find_action mmd action).Args
        let (z3lvars, _) = Z3Utils.declare_lvars args_decl z3ctx f
        let z3e = Z3Utils.build_value z3ctx z3lvars f
        Z3Utils.check_ext z3ctx z3e timeout


    let find_counterexample mmd action formulas =
        let axioms_conjectures = z3_formula_for_axioms_and_conjectures mmd
        let counterexample = ref None

        let treat_formula (i,formula) =
            let wpr = z3_formula_for_wpr mmd action formula false

            let f = WPR.Z3And (axioms_conjectures, WPR.Z3Not wpr)
            let res = check_z3_formula mmd (Some action) f 3000
        
            counterexample :=
                match res with
                | None ->
                    printfn "%i: No counterexample found!" i
                    !counterexample
                | Some (infos, env) ->
                    let former_cardinal = match !counterexample with None -> System.Int32.MaxValue | Some (_,_,infos,_) -> Model.cardinal infos
                    if Model.cardinal infos < former_cardinal
                    then Some (i, formula, infos, env)
                    else !counterexample

        List.iter treat_formula formulas
        !counterexample

    let generate_allowed_path_formula (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) formula
        action (m:Marking.Marks) prev_allowed only_terminating_run =

        // 1. Marked constraints
        let cs = z3_formula_for_constraints md mmd env m

        // 2. NOT Previous semi-generalized allowed examples
        let f = Formula.formula_from_marks env m prev_allowed true
        let f = AST.ValueNot f
        let f = MinimalAST.value2minimal md f
        let f = WPR.z3val2deterministic_formula (WPR.minimal_val2z3_val mmd f) false

        // 3. Possibly valid run: WPR & conjectures & axioms
        let wpr = z3_formula_for_wpr mmd action formula true
        let valid_run = WPR.Z3And (z3_formula_for_axioms_and_conjectures mmd, wpr)

        // 4. If we only want a terminating run...
        let trc =
            if only_terminating_run
            then
                // We know that the run will be valid for every argument value,
                // so we can just search arguments such that the run does not satisfy the weakest precondition of 'false'
                WPR.Z3Not (WPR.wpr_for_action mmd (WPR.Z3Const (AST.ConstBool false)) action false)
            else
                WPR.Z3Const (AST.ConstBool true)

        // All together
        WPR.Z3And (WPR.Z3And(cs, trc), WPR.Z3And(f,valid_run))

    let simplify_marks (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) (m:Marking.Marks) (additional_marks:Marking.Marks) =
        // We remove local vars
        let m = { m with v = Set.empty }
        // We simplify functions
        let are_marks_necessary (m:Marking.Marks) (m':Marking.Marks) =
            let m = Marking.marks_diff m m'
            let axioms_conjs = z3_formula_for_axioms_and_conjectures mmd
            let constraints = z3_formula_for_constraints md mmd env (Marking.marks_union m additional_marks)
            let funmark_constraint = z3_formula_for_constraints md mmd env m'

            let f = WPR.Z3And (WPR.Z3And (axioms_conjs, constraints), WPR.Z3Not funmark_constraint)
            match check_z3_formula_ext mmd None f 1000 with
            | Microsoft.Z3.Status.UNSATISFIABLE -> false
            | _ -> true
        let keep_funmark_if_necessary (m:Marking.Marks) (str, cvs) =
            let m' = { Marking.empty_marks with f=Set.singleton (str, cvs) }
            if are_marks_necessary m m'
            then m else Marking.marks_diff m m'
        let m = Set.fold keep_funmark_if_necessary m m.f
        // We simplify disequalities
        let keep_diff_if_necessary (m:Marking.Marks) (cv1, cv2) =
            let m' = { Marking.empty_marks with d=Set.singleton (cv1, cv2) }
            if are_marks_necessary m m'
            then m else Marking.marks_diff m m'
        Set.fold keep_diff_if_necessary m m.d

    let simplify_marks_hard (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) action formula (m:Marking.Marks) (alt_exec:List<Marking.Marks*Model.Environment>) safe =
         // We remove local vars
        let m = { m with v = Set.empty }
        // We simplify functions
        let are_marks_necessary (m:Marking.Marks) (m':Marking.Marks) =
            let m = Marking.marks_diff m m'
            let f = generate_allowed_path_formula md mmd env formula action m alt_exec (not safe)
            match check_z3_formula_ext mmd (Some action) f 1000 with
            | Microsoft.Z3.Status.UNSATISFIABLE -> false
            | _ -> true
        let keep_funmark_if_necessary (m:Marking.Marks) (str, cvs) =
            let m' = { Marking.empty_marks with f=Set.singleton (str, cvs) }
            if are_marks_necessary m m'
            then m else Marking.marks_diff m m'
        let m = Set.fold keep_funmark_if_necessary m m.f
        // We simplify disequalities
        let keep_diff_if_necessary (m:Marking.Marks) (cv1, cv2) =
            let m' = { Marking.empty_marks with d=Set.singleton (cv1, cv2) }
            if are_marks_necessary m m'
            then m else Marking.marks_diff m m'
        Set.fold keep_diff_if_necessary m m.d
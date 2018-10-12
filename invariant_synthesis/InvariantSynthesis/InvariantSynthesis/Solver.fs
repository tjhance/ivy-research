﻿module Solver

    open MinimalAST

    let decompose_marks (m:Marking.Marks) =
        let var_mark_singleton str =
            {Marking.empty_marks with v=Set.singleton str}
        let fun_mark_singleton (str, cvs) =
            {Marking.empty_marks with f=Set.singleton (str, cvs)}
        let diff_mark_singleton (cv1,cv2) =
            {Marking.empty_marks with d=Set.singleton (cv1, cv2)}
        let vms = List.map var_mark_singleton (m.v |> Set.toList)
        let fms = List.map fun_mark_singleton (m.f |> Set.toList)
        let dms = List.map diff_mark_singleton (m.d |> Set.toList)
        vms@fms@dms

    let minimal_formula_to_z3 (mmd:MinimalAST.ModuleDecl<'a,'b>) formula =
        WPR.z3ctx2deterministic_formula (WPR.minimal_val2z3_val mmd formula) false

    let z3_formula_for_constraints (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) (m:Marking.Marks) =
        let (_,_,f) = Formula.formula_for_marks env (0,Map.empty) Set.empty m
        minimal_formula_to_z3 mmd (MinimalAST.value2minimal md f)

    let z3_formula_for_axioms (mmd:MinimalAST.ModuleDecl<'a,'b>) =
        WPR.conjunction_of (WPR.conjectures_to_z3values mmd (MinimalAST.axioms_decls_to_formulas mmd.Axioms))

    let z3_formula_for_axioms_and_conjectures (mmd:MinimalAST.ModuleDecl<'a,'b>) =
        let all_invariants = MinimalAST.invariants_decls_to_formulas mmd.Invariants
        let conjectures = WPR.conjunction_of (WPR.conjectures_to_z3values mmd all_invariants)
        let axioms = z3_formula_for_axioms mmd
        WPR.Z3And (axioms, conjectures)

    [<NoComparison>]
    type SolverResult = UNSAT | UNKNOWN | SAT of Model.TypeInfos * Model.Environment

    let args_decl_for_action mmd action =
        (MinimalAST.find_action mmd action).Args

    let check_z3_formula (md:AST.ModuleDecl<'a,'b>) args_decl f timeout =
        let z3ctx = Z3Utils.build_context md
        let (z3lvars, z3concrete_map) = Z3Utils.declare_lvars args_decl z3ctx Map.empty f
        let z3e = Z3Utils.build_value z3ctx z3lvars Map.empty f
        match Z3Utils.check z3ctx z3e timeout with
        | Z3Utils.UNSAT -> UNSAT
        | Z3Utils.UNKNOWN -> UNKNOWN
        | Z3Utils.SAT m -> SAT (Z3Utils.z3model_to_ast_model md z3ctx args_decl z3lvars z3concrete_map m)

    let check_z3_disjunction (md:AST.ModuleDecl<'a,'b>) (mmd:ModuleDecl<'a,'b>) f fs timeout =
        let z3ctx = Z3Utils.build_context md

        let (z3lvars, z3concrete_map) = Z3Utils.declare_lvars [] z3ctx Map.empty f
        let z3e = Z3Utils.build_value z3ctx z3lvars Map.empty f

        let declare_lvars (action : ActionDecl, fmla : WPR.Z3Value) =
            let args_decl = action.Args
            let (z3lvars, z3concrete_map) = Z3Utils.declare_lvars_ext args_decl z3ctx Map.empty fmla (z3lvars, z3concrete_map)
            (action, Z3Utils.build_value z3ctx z3lvars Map.empty fmla, (z3lvars, z3concrete_map))
        let fs = List.map declare_lvars fs

        let es = List.map (fun (action:ActionDecl ,es,_) -> (action.Name, es)) fs
        match Z3Utils.check_disjunction z3ctx z3e es timeout with
        | (Z3Utils.UNSAT, _) -> (UNSAT, None)
        | (Z3Utils.UNKNOWN, _) -> (UNKNOWN, None)
        | (Z3Utils.SAT _, None) -> failwith "Can't retrieve action of counterexample..."
        | (Z3Utils.SAT m, Some action) ->
            let (_, _, (z3lvars, z3concrete_map)) = List.find (fun (action':ActionDecl,_,_) -> action'.Name = action) fs
            let args_decl = (MinimalAST.find_action mmd action).Args
            (SAT (Z3Utils.z3model_to_ast_model md z3ctx args_decl z3lvars z3concrete_map m), Some action)

    let z3_unsat_core (md:AST.ModuleDecl<'a,'b>) args_decl local_enums f fs timeout =
        let z3ctx = Z3Utils.build_context md

        let lenums = List.fold (fun acc e -> Z3Utils.declare_new_enumerated_type_ext e z3ctx acc) Map.empty local_enums
        let (z3lvars, z3concrete_map) = Z3Utils.declare_lvars args_decl z3ctx lenums f
        let z3e = Z3Utils.build_value z3ctx z3lvars lenums f

        let add_constraint ((z3lvars, z3concrete_map),acc) (str,f) =
            let (z3lvars, z3concrete_map) = Z3Utils.declare_lvars_ext args_decl z3ctx lenums f (z3lvars, z3concrete_map)
            let z3e = Z3Utils.build_value z3ctx z3lvars lenums f
            ((z3lvars, z3concrete_map),(str,z3e)::acc)
        let (_,z3_es) = List.fold add_constraint ((z3lvars, z3concrete_map),[]) fs
        
        Z3Utils.check_conjunction_fix z3ctx z3e z3_es timeout
    
    let find_counterexample_action md mmd (action : ActionDecl) formulas =
        let axioms_conjectures = z3_formula_for_axioms_and_conjectures mmd
        let counterexample = ref None

        let treat_formula (i,formula) =
            if not (Option.isSome !counterexample) then
                let f = WPR.Z3And (axioms_conjectures, WPR.wpr_for_action mmd (minimal_formula_to_z3 mmd formula) action true)
                let res = check_z3_formula md action.Args f 3000
            
                counterexample :=
                    match res with
                    | UNSAT | UNKNOWN -> !counterexample
                    | SAT (infos, env) ->
                        let former_cardinal = match !counterexample with None -> System.Int32.MaxValue | Some (_,_,infos,_) -> Model.cardinal infos
                        if Model.cardinal infos < former_cardinal
                        then Some (i, formula, infos, env)
                        else !counterexample

        List.iter treat_formula formulas
        !counterexample

    let find_counterexample md mmd formulas =
        let axioms_conjectures = z3_formula_for_axioms_and_conjectures mmd 
        let counterexample = ref None

        let treat_formula (i,formula) =
            let fs =
              List.map (fun (action: ActionDecl) ->
                (action,
                 WPR.wpr_for_action mmd (minimal_formula_to_z3 mmd formula) action true)
              ) (mmd.Actions)
            let res = check_z3_disjunction md mmd axioms_conjectures fs 3000

            counterexample :=
                match res with
                | (UNSAT, _) | (UNKNOWN, _) -> !counterexample
                | (SAT (infos, env), Some action) ->
                    let former_cardinal = match !counterexample with None -> System.Int32.MaxValue | Some (_,_,_,infos,_) -> Model.cardinal infos
                    if Model.cardinal infos < former_cardinal
                    then Some (i, action, formula, infos, env)
                    else !counterexample
                | (SAT _, None) -> failwith "Can't retrieve the main action of the counterexample."

        List.iter treat_formula formulas
        !counterexample

    let not_already_allowed_state_formula (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) common_cvs allowed_execs =
        let f = Formula.generate_semi_generalized_formulas common_cvs (0, Map.empty) allowed_execs
        let f = AST.ValueNot f
        let f = MinimalAST.value2minimal md f
        minimal_formula_to_z3 mmd f

    let wpr_for_actions mmd formula =
        let wprs = List.map (fun (action:ActionDecl) -> WPR.wpr_for_action mmd formula action false) mmd.Actions
        WPR.conjunction_of wprs

    let wpr_based_valid_state_formula (mmd:MinimalAST.ModuleDecl<'a,'b>) formula =
        let wpr = wpr_for_actions mmd (minimal_formula_to_z3 mmd formula)
        WPR.Z3And (z3_formula_for_axioms_and_conjectures mmd, wpr)

    let wpr_based_invalid_state_formula (mmd:MinimalAST.ModuleDecl<'a,'b>) formula =
        let wpr = WPR.Z3Not (wpr_for_actions mmd (minimal_formula_to_z3 mmd formula))
        WPR.Z3And (z3_formula_for_axioms_and_conjectures mmd, wpr)

    let terminating_or_failing_run_formula (mmd:MinimalAST.ModuleDecl<'a,'b>) action =
        WPR.wpr_for_action mmd (WPR.Z3Const (AST.ConstBool false)) action true

    let find_allowed_execution (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) formula
        action (m:Marking.Marks) common_cvs prev_allowed only_terminating_run =

        if common_cvs <> (Formula.concrete_values_of_marks env m) then failwith "Some common values does not appear in any constraint..."

        // 1. Marked constraints
        let cs = z3_formula_for_constraints md mmd env m
        // 2. NOT previous allowed state
        let f = not_already_allowed_state_formula md mmd common_cvs prev_allowed
        // 3. Possibly valid state
        let valid_run = wpr_based_valid_state_formula mmd formula
        // 4. If we only want a terminating run...
        let trc =
            if only_terminating_run
            then
                terminating_or_failing_run_formula mmd action
            else
                WPR.Z3Const (AST.ConstBool true)
        // All together
        let f = WPR.Z3And (WPR.Z3And(cs, trc), WPR.Z3And(f,valid_run))
        // Solve!
        match check_z3_formula md action.Args f 3000 with
        | UNSAT | UNKNOWN -> None
        | SAT (i,e) -> Some (i,e)

    let simplify_marks (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) (m:Marking.Marks) (additional_marks:Marking.Marks) =
        let axioms_conjs = z3_formula_for_axioms_and_conjectures mmd
        let are_marks_necessary (m:Marking.Marks) (m':Marking.Marks) =
            let m = Marking.marks_diff m m'
            let constraints = z3_formula_for_constraints md mmd env (Marking.marks_union m additional_marks)
            let tested_constraint = z3_formula_for_constraints md mmd env m'
            let f = WPR.Z3And (WPR.Z3And (axioms_conjs, constraints), WPR.Z3Not tested_constraint)
            match check_z3_formula md [] f 1000 with
            | UNSAT -> false
            | _ -> true
        let keep_mark_if_necessary (m:Marking.Marks) m' =
            if are_marks_necessary m m'
            then m else Marking.marks_diff m m'
        List.fold keep_mark_if_necessary m (decompose_marks m)

    let expand_marks (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) infos (env:Model.Environment) (m:Marking.Marks) =
        // We add every valid fun/diff constraint!
        let cs = z3_formula_for_constraints md mmd env m
        let axioms_conjs = z3_formula_for_axioms_and_conjectures mmd
        let f = WPR.Z3And (cs, axioms_conjs)
        let is_formula_valid f' =
            let f = WPR.Z3And (f, WPR.Z3Not f')
            match check_z3_formula md [] f 1000 with
            | UNSAT ->
                // We don't add mark if t can be deduced directly from the axioms
                let f = WPR.Z3And (axioms_conjs, WPR.Z3Not f')
                match check_z3_formula md [] f 1000 with
                | SAT _ -> true
                | _ -> false
            | _ -> false
        let is_mark_valid m =
            let f = z3_formula_for_constraints md mmd env m
            is_formula_valid f

        let fm = List.map (fun (k,_) -> k) (Map.toList env.f) |> Set.ofList
        let diffs = Set.unionMany (List.map (fun t -> Marking.all_potential_diffs_for_type md.Types infos t) (AST.all_uninterpreted_types md.Types))
        let m = { Marking.empty_marks with Marking.d = diffs ; Marking.f = fm }
        let ms = decompose_marks m
        let ms = List.filter is_mark_valid ms
        Marking.marks_union_many ms
        // TODO: marks (=constraints) should be partially sorted by decreasing order of "strength" (for instance, `<' is weaker than `succ')

    let wpr_based_minimization (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) infos (env:Model.Environment) action
        formula (m:Marking.Marks) common_cvs (alt_exec:List<Marking.Marks*Model.Environment>) only_consider_terminating_runs =
        
        let save_m = m
        let m = expand_marks md mmd infos env m // We expand marks so some weak constraints can be kept instead of stronger constraints
        
        // Unsat core!
        let f = not_already_allowed_state_formula md mmd common_cvs alt_exec
        let f = WPR.Z3And (f, wpr_based_valid_state_formula mmd formula)
        let f =
            if only_consider_terminating_runs
            then WPR.Z3And (f, terminating_or_failing_run_formula mmd action)
            else f

        let ms = decompose_marks m
        let labeled_ms = List.mapi (fun i m -> (sprintf "%i" i, m)) ms
        let labeled_cs = List.map (fun (i,m) -> (i, z3_formula_for_constraints md mmd env m)) labeled_ms

        match z3_unsat_core md action.Args [] f labeled_cs 5000 with
        | (Z3Utils.SolverResult.UNSAT, lst) ->
            let labeled_ms = List.filter (fun (str,_) -> List.contains str lst) labeled_ms
            let ms = List.map (fun (_,m) -> m) labeled_ms
            Marking.marks_union_many ms
        | (Z3Utils.SolverResult.UNKNOWN _, _) ->
            printfn "Can't resolve unSAT core!"
            save_m
        | (Z3Utils.SolverResult.SAT _, _) ->
            printfn "Minimization impossible: the core is SAT."
            save_m
    
    let minimize_marks m eval_f =
        if eval_f m
        then
            let keep_mark_if_necessary (m:Marking.Marks) m' =
                let m' = Marking.marks_diff m m'
                if eval_f m'
                then m' else m
            Some (List.fold keep_mark_if_necessary m (decompose_marks m))
        else None

    let wpr_based_minimization_existential_part (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) infos (env:Model.Environment)
        formula (m:Marking.Marks) common_cvs env' m' =

        let save_m' = m'
        let m' = expand_marks md mmd infos env' (Marking.marks_union m m')
        let m' = Marking.marks_diff m' (expand_marks md mmd infos env m)

        let not_valid_state = wpr_based_invalid_state_formula mmd formula
        let counterexample_state = z3_formula_for_constraints md mmd env m
        let base_f = WPR.Z3And (not_valid_state, counterexample_state)
        let give_correct_invariant m' =
            let f = minimal_formula_to_z3 mmd (MinimalAST.value2minimal md (Formula.generate_invariant env common_cvs m [(m',env')]))
            let f = WPR.Z3And (base_f, f)
            match check_z3_formula md [] f 5000 with
            | SolverResult.UNKNOWN ->
                printfn "Can't decide of satisfiability!"
                false
            | SolverResult.UNSAT -> true
            | SolverResult.SAT _ -> false

        match minimize_marks m' give_correct_invariant with
        | None ->
            printfn "Minimization impossible: the core is SAT."
            save_m'
        | Some m' -> m'

    let has_k_exec_counterexample_formula mmd formula boundary =

        let rec compute_next_iterations fs n =
            match n with
            | n when n <= 0 -> (*printfn "All paths have been computed!" ;*) fs
            | n ->
                //printfn "Computing level %i..." n
                let prev = List.head fs
                let wpr = wpr_for_actions mmd prev
                compute_next_iterations (wpr::fs) (n-1)

        let paths = compute_next_iterations [formula] boundary
        let f = WPR.conjunction_of paths
        // Add initializations
        let f = List.fold (fun f (init_action:ActionDecl) -> WPR.wpr_for_action mmd f init_action false) f mmd.InitActions
        WPR.Z3Not f
        
    let sbv_based_minimization (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) infos (env:Model.Environment) (m:Marking.Marks) common_cvs (alt_exec:List<Marking.Marks*Model.Environment>) boundary =

        let save_m = m
        let m = expand_marks md mmd infos env m // We expand marks so some weak constraints can be kept instead of stronger constraints

        let axioms = z3_formula_for_axioms mmd
        let give_k_invariant m =
            let f = minimal_formula_to_z3 mmd (MinimalAST.value2minimal md (Formula.generate_invariant env common_cvs m alt_exec))
            let f = WPR.Z3And (axioms, has_k_exec_counterexample_formula mmd f boundary)
            match check_z3_formula md [] f 5000 with
            | SolverResult.UNKNOWN ->
                printfn "Can't decide of satisfiability!"
                false
            | SolverResult.UNSAT -> true
            | SolverResult.SAT _ -> false

        match minimize_marks m give_k_invariant with
        | None ->
            printfn "ERROR: The whole formula is not a k-invariant!"
            save_m
        | Some m -> m

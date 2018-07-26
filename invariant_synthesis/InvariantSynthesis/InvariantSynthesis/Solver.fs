module Solver

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

    let z3_formulas_for_constraints (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) (m:Marking.Marks) =
        let var_constraint str = // Constraints on the arguments
            let cv = Map.find str env.v
            AST.ValueEqual (AST.ValueVar str, AST.ValueConst cv)
        let vcs = List.map var_constraint (m.v |> Set.toList)
        let fun_constraint (str, cvs) =
            let cv = Map.find (str, cvs) env.f
            let vs = List.map (fun cv -> AST.ValueConst cv) cvs
            AST.ValueEqual (AST.ValueFun (str, vs), AST.ValueConst cv)
        let fcs = List.map fun_constraint (m.f |> Set.toList)
        let diff_constraint (cv1, cv2) =
            AST.ValueNot (AST.ValueEqual (AST.ValueConst cv1, AST.ValueConst cv2))
        let dcs = List.map diff_constraint (m.d |> Set.toList)
        let cs = vcs@fcs@dcs
        let cs = List.map (MinimalAST.value2minimal md) cs
        List.map (fun c -> WPR.z3val2deterministic_formula (WPR.minimal_val2z3_val mmd c) false) cs

    let z3_formula_for_constraints (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) (m:Marking.Marks) =
        WPR.conjunction_of (z3_formulas_for_constraints md mmd env m)

    let z3_fomula_for_axioms (mmd:MinimalAST.ModuleDecl<'a,'b>) =
        WPR.conjunction_of (WPR.conjectures_to_z3values mmd (MinimalAST.axioms_decls_to_formulas mmd.Axioms))

    let z3_formula_for_axioms_and_conjectures (mmd:MinimalAST.ModuleDecl<'a,'b>) =
        let all_invariants = MinimalAST.invariants_decls_to_formulas mmd.Invariants
        let conjectures = WPR.conjunction_of (WPR.conjectures_to_z3values mmd all_invariants)
        let axioms = z3_fomula_for_axioms mmd
        WPR.Z3And (axioms, conjectures)

    let z3_formula_for_wpr (mmd:MinimalAST.ModuleDecl<'a,'b>) action formula uq_args =
        let z3formula = WPR.z3val2deterministic_formula (WPR.minimal_val2z3_val mmd formula) false
        WPR.wpr_for_action mmd z3formula action uq_args

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

    let check_z3_disjunction (md:AST.ModuleDecl<'a,'b>) f fs timeout =
        let z3ctx = Z3Utils.build_context md

        let (z3lvars, z3concrete_map) = Z3Utils.declare_lvars [] z3ctx Map.empty f
        let z3e = Z3Utils.build_value z3ctx z3lvars Map.empty f

        let declare_lvars (mmd, action, f) =
            let args_decl = (MinimalAST.find_action mmd action).Args
            let (z3lvars, z3concrete_map) = Z3Utils.declare_lvars_ext args_decl z3ctx Map.empty f (z3lvars, z3concrete_map)
            (mmd, action, Z3Utils.build_value z3ctx z3lvars Map.empty f, (z3lvars, z3concrete_map))
        let fs = List.map declare_lvars fs

        let es = List.map (fun (_,action,es,_) -> (action, es)) fs
        match Z3Utils.check_disjunction z3ctx z3e es timeout with
        | (Z3Utils.UNSAT, _) -> (UNSAT, None)
        | (Z3Utils.UNKNOWN, _) -> (UNKNOWN, None)
        | (Z3Utils.SAT _, None) -> failwith "Can't retrieve action of counterexample..."
        | (Z3Utils.SAT m, Some action) ->
            let (mmd, _, _, (z3lvars, z3concrete_map)) = List.find (fun (_,action',_,_) -> action' = action) fs
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
    
    let find_counterexample_action md mmd action formulas =
        let axioms_conjectures = z3_formula_for_axioms_and_conjectures mmd
        let counterexample = ref None

        let treat_formula (i,formula) =
            let wpr = z3_formula_for_wpr mmd action formula false
            let f = WPR.Z3And (axioms_conjectures, WPR.Z3Not wpr)
            let res = check_z3_formula md (args_decl_for_action mmd action) f 3000
        
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

    let find_counterexample md mmds formulas =
        let (_,tmp_mmd) = (List.head (Map.toList mmds)) // We arbitrary take axioms and conjectures of the first mmd (they should be exactly the same for every mmd)
        let axioms_conjectures = z3_formula_for_axioms_and_conjectures tmp_mmd
        let counterexample = ref None

        let treat_formula (i,formula) =
            let fs = List.map (fun (action,mmd) -> (mmd, action, WPR.Z3Not (z3_formula_for_wpr mmd action formula false))) (Map.toList mmds)
            let res = check_z3_disjunction md axioms_conjectures fs 3000
            
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

    let not_already_allowed_state_formula (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) (m:Marking.Marks) allowed_execs =
        let f = Formula.formula_from_marks env m allowed_execs true
        let f = AST.ValueNot f
        let f = MinimalAST.value2minimal md f
        WPR.z3val2deterministic_formula (WPR.minimal_val2z3_val mmd f) false

    let wpr_based_valid_state_formula (mmd:MinimalAST.ModuleDecl<'a,'b>) action other_actions formula =
        let wpr = z3_formula_for_wpr mmd action formula true
        let add_wpr acc (action',mmd') =
            if action' <> action
            then
                let wpr = z3_formula_for_wpr mmd' action' formula true
                WPR.Z3And (acc, wpr)
            else acc
        let wpr = List.fold add_wpr wpr other_actions
        WPR.Z3And (z3_formula_for_axioms_and_conjectures mmd, wpr)

    let terminating_or_failing_run_formula (mmd:MinimalAST.ModuleDecl<'a,'b>) action =
        WPR.Z3Not (WPR.wpr_for_action mmd (WPR.Z3Const (AST.ConstBool false)) action false)

    let find_allowed_execution (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) formula
        action (m:Marking.Marks) other_actions prev_allowed only_terminating_run =

        // 1. Marked constraints
        let cs = z3_formula_for_constraints md mmd env m
        // 2. NOT previous allowed state
        let f = not_already_allowed_state_formula md mmd env m prev_allowed
        // 3. Possibly valid state
        let valid_run = wpr_based_valid_state_formula mmd action other_actions formula
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
        match check_z3_formula md (args_decl_for_action mmd action) f 3000 with
        | UNSAT | UNKNOWN -> None
        | SAT (i,e) -> Some (i,e)

    let simplify_marks (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) (m:Marking.Marks) (additional_marks:Marking.Marks) =
        // We remove local vars
        let m = { m with v = Set.empty }
        // We simplify functions
        let axioms_conjs = z3_formula_for_axioms_and_conjectures mmd
        let are_marks_necessary (m:Marking.Marks) (m':Marking.Marks) =
            let m = Marking.marks_diff m m'
            let constraints = z3_formula_for_constraints md mmd env (Marking.marks_union m additional_marks)
            let tested_constraint = z3_formula_for_constraints md mmd env m'
            let f = WPR.Z3And (WPR.Z3And (axioms_conjs, constraints), WPR.Z3Not tested_constraint)
            match check_z3_formula md [] f 1000 with
            | UNSAT -> false
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

    let expand_marks (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) infos (env:Model.Environment) (m:Marking.Marks) =
        // We remove local vars
        let m = { m with v = Set.empty }
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
        let is_funmark_valid (str, cvs) =
            let m = { Marking.empty_marks with f=Set.singleton (str, cvs) }
            let f = z3_formula_for_constraints md mmd env m
            is_formula_valid f
        let is_diff_valid (cv1, cv2) =
            let m = { Marking.empty_marks with d=Set.singleton (cv1, cv2) }
            let f = z3_formula_for_constraints md mmd env m
            is_formula_valid f

        let fm = List.map (fun (k,_) -> k) (Map.toList env.f)
        let fm = List.filter is_funmark_valid fm
        let diffs = Set.unionMany (List.map (fun (d:AST.TypeDecl) -> Formula.all_diffs_for_type md.Types infos (AST.Uninterpreted d.Name)) md.Types)
        let diffs = Set.filter is_diff_valid diffs
        { Marking.empty_marks with f = fm |> Set.ofList ; d = diffs }

    type MinimizationMode = Safe | Hard | MinimizeAltExec
    let wpr_based_minimization (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) infos (env:Model.Environment) action other_actions formula (m:Marking.Marks) (alt_exec:List<Marking.Marks*Model.Environment>) (mode:MinimizationMode) =
        
        let m = { m with v = Set.empty } // We remove local vars
        let save_m = m
        let m = expand_marks md mmd infos env m // We expand marks!
        
        // Unsat core!
        let f =
            match mode with
            | Safe | Hard ->
                let f = not_already_allowed_state_formula md mmd env m alt_exec
                let f = WPR.Z3And (f, wpr_based_valid_state_formula mmd action other_actions formula)
                if mode = Hard
                then WPR.Z3And (f, terminating_or_failing_run_formula mmd action)
                else f
            | MinimizeAltExec ->
                let not_valid_run = WPR.Z3Not (wpr_based_valid_state_formula mmd action other_actions formula)
                let f = z3_formula_for_constraints md mmd env m
                WPR.Z3And (f, not_valid_run)

        let (save_m, m, env) =
            if mode = MinimizeAltExec then
                assert (List.length alt_exec = 1)
                let (m', env) = List.head alt_exec
                let m' = { m' with v = Set.empty } // We remove local vars
                let save_m = m'
                let m' = expand_marks md mmd infos env (Marking.marks_union m m') // We expand marks!
                (save_m,Marking.marks_diff m' m, env)
            else (save_m, m, env)

        let ms = decompose_marks m
        let labeled_ms = List.mapi (fun i m -> (sprintf "%i" i, m)) ms
        let labeled_cs = List.map (fun (i,m) -> (i, z3_formula_for_constraints md mmd env m)) labeled_ms

        match z3_unsat_core md (args_decl_for_action mmd action) [] f labeled_cs 5000 with
        | (Z3Utils.SolverResult.UNSAT, lst) ->
            let labeled_ms = List.filter (fun (str,_) -> List.contains str lst) labeled_ms
            let ms = List.map (fun (_,m) -> m) labeled_ms
            Marking.marks_union_many ms
        | (Z3Utils.SolverResult.UNKNOWN _, _) ->
            printfn "Can't resolve unSAT core!"
            save_m
        | (Z3Utils.SolverResult.SAT _, _) ->
            printfn "Core is SAT."
            save_m
        // TODO: run unsat core only for constraints on functions, and then run unsat core for disequalities on the result?

    let has_valid_k_execution_formula formula actions init_actions boundary =

        // Action enum
        let actions_enum = AST.generated_name (sprintf "__action_enum")
        let actions_enum_vals = List.init (List.length actions) (fun i -> AST.compose_name actions_enum (sprintf "%i" i))
        let actions_enum_map = List.fold2 (fun acc (str,_) e_str -> Map.add str e_str acc) Map.empty actions actions_enum_vals
        // Level enum
        let levels_enum = AST.generated_name (sprintf "__level_enum")
        let levels_enum_vals = List.init (boundary+1) (fun i -> AST.compose_name levels_enum (sprintf "%i" i))
        let (levels_enum_map,_) = List.fold (fun (acc,i) e_str -> (Map.add i e_str acc, i+1)) (Map.empty,0) levels_enum_vals
        let new_enums = [(actions_enum, actions_enum_vals);(levels_enum, levels_enum_vals)]

        let rename_vars mmd action suffix f =
            let args_decl = args_decl_for_action mmd action
            let dico = List.fold (fun acc (v:AST.VarDecl) -> Map.add v.Name (AST.make_name_unique_bis v.Name suffix) acc) Map.empty args_decl
            let renaming = Map.map (fun _ v -> WPR.Z3Var v) dico
            (WPR.map_vars_in_z3value f renaming, List.map (fun (d:AST.VarDecl) -> AST.default_var_decl (Map.find d.Name dico) d.Type) (args_decl) |> Set.ofList)

        let rec compute_next_iterations (fs,new_vars) n =
            match n with
            | n when n <= 0 -> (*printfn "All paths have been computed!" ;*) (fs, new_vars)
            | n ->
                //printfn "Computing level %i..." n
                let prev = List.head fs
                let add_wpr (f,new_vars) (action,mmd) =
                    let wpr = WPR.wpr_for_action mmd prev action false
                    let (wpr, new_vars') = rename_vars mmd action (sprintf "lev_%i" n) wpr
                    let new_vars = Set.union new_vars new_vars'
                    let action_selection_var = AST.default_var_decl (AST.generated_name (sprintf "__action_selection_%i" n)) (AST.Enumerated actions_enum)
                    let new_vars = Set.add action_selection_var new_vars
                    (WPR.Z3Or (f, WPR.Z3And (wpr, WPR.Z3Equal(WPR.Z3Var action_selection_var.Name, WPR.Z3Const (AST.ConstEnumerated (actions_enum, Map.find action actions_enum_map))))), new_vars)
                let (wpr, new_vars) = List.fold add_wpr (WPR.Z3Const (AST.ConstBool false),new_vars) actions
                compute_next_iterations (wpr::fs,new_vars) (n-1)

        let (paths, new_vars) = compute_next_iterations ([formula], Set.empty) boundary
        let add_length_constr (paths, new_vars, i) f =
            let length_selection_var = AST.default_var_decl (AST.generated_name "__length_selection") (AST.Enumerated levels_enum)
            let new_vars = Set.add length_selection_var new_vars
            let f = WPR.Z3And (f, WPR.Z3Equal(WPR.Z3Var length_selection_var.Name, WPR.Z3Const (AST.ConstEnumerated (levels_enum, Map.find i levels_enum_map))))
            (f::paths, new_vars, i+1)
        let (paths, new_vars, _) = List.fold add_length_constr ([],new_vars, 0) paths
        let f = WPR.disjunction_of paths

        // Add initializations
        let add_init (f, new_vars) (action,mmd) =
            let f = WPR.wpr_for_action mmd f action false
            let (f, new_vars') = rename_vars mmd action (sprintf "init_%s" action) f
            let new_vars = Set.union new_vars new_vars'
            (f, new_vars)
        let (f, new_vars) = List.fold add_init (f, new_vars) init_actions

        (f, new_vars, new_enums)
        
    let sbv_based_minimization (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) infos (env:Model.Environment) actions init_actions (m:Marking.Marks) (alt_exec:List<Marking.Marks*Model.Environment>) boundary =

        let m = { m with v = Set.empty } // We remove local vars
        let save_m = m
        let m = expand_marks md mmd infos env m // We expand marks!

        // Base assumptions
        let axioms = z3_fomula_for_axioms mmd
        let f = not_already_allowed_state_formula md mmd env m alt_exec
        let f = WPR.Z3And (axioms,f)
        // TODO: Fix the following condition (it does not do what is expected)
        let (break_assumption, new_vars, new_enums) = has_valid_k_execution_formula (WPR.Z3Const (AST.ConstBool false)) actions init_actions boundary
        let f = WPR.Z3And (f, WPR.Z3Not break_assumption) // We don't want the execution to be valid only because it breaks an assumption

        // UnSAT core
        let formula_for_marks m =
            let f = z3_formula_for_constraints md mmd env m
            let (f, _, _) = has_valid_k_execution_formula f actions init_actions boundary
            f

        let ms = decompose_marks m
        let labeled_ms = List.mapi (fun i m -> (sprintf "%i" i, m)) ms
        let labeled_cs = List.map (fun (i,m) -> (i, formula_for_marks m)) labeled_ms
        printfn "Solving unSAT core..."

        match z3_unsat_core md (Set.toList new_vars) new_enums f labeled_cs 25000 with
        | (Z3Utils.SolverResult.UNSAT, lst) ->
            let labeled_ms = List.filter (fun (str,_) -> List.contains str lst) labeled_ms
            let ms = List.map (fun (_,m) -> m) labeled_ms
            Marking.marks_union_many ms
        | (Z3Utils.SolverResult.UNKNOWN, _) ->
            printfn "Can't resolve unSAT core!"
            save_m
        | (Z3Utils.SolverResult.SAT _, _) ->
            printfn "Error: Core is SAT..."
            save_m
        
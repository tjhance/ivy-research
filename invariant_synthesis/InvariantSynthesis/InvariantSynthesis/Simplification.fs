module Simplification

    let z3_formula_for_constraints (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) (m:Synthesis.Marks) =
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
        let (z3lvars, z3concrete_map) =
            match action with
            | None -> Z3Utils.empty_lvars
            | Some action -> Z3Utils.declare_lvars mmd action z3ctx f
        let z3e = Z3Utils.build_value z3ctx z3lvars f
        match Z3Utils.check z3ctx z3e timeout with
        | None -> None
        | Some m ->
            let args_decl =
                match action with
                | None -> []
                | Some action -> (MinimalAST.find_action mmd action).Args
            let (infos, env) = Z3Utils.z3model_to_ast_model mmd z3ctx args_decl z3lvars z3concrete_map m
            Some (infos, env)

    let simplify_marks (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) (m:Synthesis.Marks) (additional_marks:Synthesis.Marks) =
        // We remove local vars
        let m = { m with v = Set.empty }
        // We simplify functions
        let is_funmark_necessary (m:Synthesis.Marks) (str, cvs) =
            let m = { m with f = Set.remove (str, cvs) m.f }
            let axioms_conjs = z3_formula_for_axioms_and_conjectures mmd
            let constraints = z3_formula_for_constraints md mmd env (Synthesis.marks_union m additional_marks)
            let funmark_constraint = z3_formula_for_constraints md mmd env { Synthesis.empty_marks with f = Set.singleton (str, cvs) }

            let f = WPR.Z3And (WPR.Z3And (axioms_conjs, constraints), WPR.Z3Not funmark_constraint)
            match check_z3_formula mmd None f 1000 with
            | None -> true
            | Some _ -> false

        let m = Set.fold (fun acc k -> if is_funmark_necessary acc k then acc else { acc with f = Set.remove k acc.f }) m m.f
        // TODO
        m

    let simplify_marks_hard (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) action (m:Synthesis.Marks) (alt_exec:List<Synthesis.Marks*Model.Environment>) =
        // TODO
        m
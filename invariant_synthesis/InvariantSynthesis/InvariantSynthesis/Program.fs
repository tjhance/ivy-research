open System.Text
open System
open AST

type ModuleDecl = ModuleDecl<Model.TypeInfos,Model.Environment>

let read_until_line_jump () =
    let str = new StringBuilder()
    let line = ref "_"
    while !line <> "" do
        line := Console.ReadLine()
        ignore (str.Append(!line + Environment.NewLine))
    str.ToString()

// ----- MANUAL MODE -----

let manual_counterexample (md:ModuleDecl) decls possible_actions mmds verbose =
    printfn "Please enter constraints:"
    let str = read_until_line_jump ()
    printfn "Loading constraints..."
    let cs = ConstraintsParser.parse_from_str md str
    printfn "Building environment from constraints..."
    let (infos, env) = Model.constraints_to_env md cs
    if verbose
    then
        printfn "%A" infos
        printfn "%A" env

    printfn "Which action do you want to analyze?"
    List.iteri (fun i str -> printfn "%i. %s" i str) possible_actions
    let nb = Convert.ToInt32 (Console.ReadLine())
    let action = List.item nb possible_actions

    let args_decl = (find_action md action "").Args
    let env =
        List.fold
            (
                fun (acc:Model.Environment) vd ->
                    printfn "Please enter next arg:"
                    let cv =
                        match vd.Type with
                        | Void -> ConstVoid
                        | Bool -> ConstBool (Convert.ToBoolean (Console.ReadLine()))
                        | Uninterpreted str -> ConstInt (str, Convert.ToInt32 (Console.ReadLine()))
                        | Enumerated str -> ConstEnumerated (str, Console.ReadLine())
                    { acc with v = Map.add vd.Name cv acc.v }
            )
            env args_decl
    
    let mmd = Map.find action mmds

    printfn "Executing..."
    let tr = TInterpreter.trace_action mmd infos env action (List.map (fun (d:VarDecl) -> MinimalAST.ValueVar d.Name) args_decl) AST.impossible_var_factor
    let env' = Trace.final_env tr
    if verbose
    then
        printfn "%A" env'

    if Trace.is_fully_executed tr
    then
        printfn "Please enter the index of the invariant to analyze:"
        let (main_module,_) = AST.decompose_name action
        let invs = AST.find_invariants md main_module
        List.iteri
            (
                fun i (d:AST.InvariantDecl) ->
                    let mv = MinimalAST.value2minimal md d.Formula
                    match Interpreter.evaluate_value mmd infos env' mv with
                    | ConstBool true -> Console.ForegroundColor <- ConsoleColor.Green
                    | ConstBool false -> Console.ForegroundColor <- ConsoleColor.Red
                    | _ -> Console.ResetColor()
                    printfn "%i. [%s] %s" i d.Module (Printer.value_to_string decls d.Formula 0)
            ) invs
        Console.ResetColor()

        let nb = Convert.ToInt32 (Console.ReadLine())
        let formula = List.item nb (AST.invariants_to_formulas invs)
        let formula = MinimalAST.value2minimal md formula
        Some (action, infos, env, cs, formula, tr)
    else
        Some (action, infos, env, cs, MinimalAST.ValueConst (ConstBool true), tr)

let marks_to_string decls (env:Model.Environment) (m:Marking.Marks) =
  let res = Set.fold (fun acc v -> sprintf "%s%s\n" acc (Printer.varmark_to_string decls env v)) "" m.v
  let res = Set.fold (fun acc f -> sprintf "%s%s\n" acc (Printer.funmark_to_string decls env f)) res m.f
  res
    
let manual_allowed_path (md:ModuleDecl) decls (env:Model.Environment) cs m um =
    printfn "Please modify some constraints on the environment to change the final formula value."
    printfn ""
    printfn "Constraints you can't change:"
    printfn "%s" (marks_to_string decls env m)
    printfn ""
    printfn "Constraints you should change (at least one):"
    printfn "%s" (marks_to_string decls env um)

    printfn ""
    let str = read_until_line_jump ()
    printfn "Loading constraints..."
    let cs' = ConstraintsParser.parse_from_str md str
    printfn "Building new environment..."
    let (infos_allowed, env_allowed) = Model.constraints_to_env md (cs@cs')
    printfn "Computing..."
    Some (infos_allowed, { env_allowed with v=env.v }) // We keep the same args as before

// ----- AUTO MODE -----

let auto_counterexample (md:ModuleDecl) decls main_module mmds =
    let counterexample = ref None
    let first_loop = ref true
    let finished = ref false

    let invs = AST.find_invariants md main_module

    while not (!finished) do
        printfn "loopin..."

        let formulas =
            if !first_loop
            then
                first_loop := false
                //printfn "Searching assertions fail..."
                Some [(-1,MinimalAST.ValueConst (ConstBool true))]
            else
                (*
                printfn "Select the conjecture(s) to test (separated by space, '*' for all):"
                List.iteri (fun i (d:AST.InvariantDecl) -> printfn "%i. [%s] %s" i d.Module (Printer.value_to_string decls d.Formula 0)) invs
                let line = Console.ReadLine()
                *)
                let line = "*"
                let nbs =
                    if line = "*"
                    then List.mapi (fun i _ -> sprintf "%i" i) invs
                    else line.Split ([|' '|], StringSplitOptions.RemoveEmptyEntries) |> List.ofArray
                if List.isEmpty nbs
                then None
                else
                    let nbs = List.map (fun (str:string) -> Convert.ToInt32 str) nbs
                    let formulas = List.map (fun nb -> (nb,List.item nb (AST.invariants_to_formulas invs))) nbs
                    let formulas = List.map (fun (nb,formula) -> (nb,MinimalAST.value2minimal md formula)) formulas
                    Some formulas

        match formulas with
        | None -> finished := true
        | Some formulas ->
            match Solver.find_counterexample md mmds formulas with
            | None -> counterexample := None
            | Some c -> finished := true ; counterexample := Some c

    match !counterexample with
    | None -> None
    | Some (i, action, formula, infos, env) ->
        let mmd = Map.find action mmds
        let action_args = (MinimalAST.find_action mmd action).Args
        printfn "Invariant n°%i: %s" i action
        let tr = TInterpreter.trace_action mmd infos env action (List.map (fun (d:VarDecl) -> MinimalAST.ValueVar d.Name) action_args) AST.impossible_var_factor
        Some (action, infos, env, [], formula, tr)

let auto_allowed_path (md:ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) formula
    action (m:Marking.Marks) all_actions prev_allowed only_terminating_run =
    Solver.find_allowed_execution md mmd env formula action m all_actions prev_allowed only_terminating_run


// ----- MAIN -----

let analyse_example_ending mmd decls infos tr formula =
    let env' = Trace.final_env tr
    if Trace.is_fully_executed tr
    then
        let (b,cfgs) = Marking.marks_for_value mmd decls infos env' Set.empty formula
        let cfg = Marking.best_cfg cfgs
        if b <> ConstBool true && b <> ConstBool false
        then failwith "Invalid execution!"
        (b = ConstBool true, true, cfg)
    else
        (Trace.assume_failed tr, false, Marking.empty_config)

let eq a b = WPR.Z3Equal (a,b)
let ne a b = WPR.Z3Not (WPR.Z3Equal (a,b))
let a = WPR.Z3Var "A"
let b = WPR.Z3Var "B"
let c = WPR.Z3Var "C"
let aid = WPR.Z3Var "AID"
let bid = WPR.Z3Var "BID"
let cid = WPR.Z3Var "CID"
let int_to_node i = match i with | 0 -> a | 1 -> b | 2 -> c | _ -> failwith "fail"
let int_to_id i = match i with | 0 -> aid | 1 -> bid | 2 -> cid | _ -> failwith "fail"
let leader a = WPR.Z3Fun ("leader", [int_to_node a])
let pnd b c = WPR.Z3Fun ("pnd", [int_to_id b; int_to_node c])
let nid a = WPR.Z3Fun ("nid", [int_to_node a])
let btw a b c = WPR.Z3Fun ("btw", [int_to_node a; int_to_node b; int_to_node c])
let n a = WPR.Z3Not a
let le a b = WPR.Z3Not (WPR.Z3Fun ("id.<", [b; a]))
let testing =
    WPR.Z3Forall ({Name="A"; Type=Uninterpreted "node"; Representation={DisplayName=None; Flags=Set.empty}},
      WPR.Z3Forall ({Name="B"; Type=Uninterpreted "node"; Representation={DisplayName=None; Flags=Set.empty}},
        WPR.Z3Forall ({Name="C"; Type=Uninterpreted "node"; Representation={DisplayName=None; Flags=Set.empty}},
          WPR.Z3Forall ({Name="AID"; Type=Uninterpreted "id"; Representation={DisplayName=None; Flags=Set.empty}},
            WPR.Z3Forall ({Name="BID"; Type=Uninterpreted "id"; Representation={DisplayName=None; Flags=Set.empty}},
              WPR.Z3Forall ({Name="CID"; Type=Uninterpreted "id"; Representation={DisplayName=None; Flags=Set.empty}},
                n (
                          AwesomeMinimize.and_list [
                            ne a b;
                            ne b c;
                            ne c a;
                            ne aid bid;
                            ne bid cid;
                            ne aid cid;
                            n (leader 0);
                            n (leader 1);
                            n (leader 2);
                            le aid aid;
                            le aid bid;
                            le aid cid;
                            le bid bid;
                            le bid cid;
                            le cid cid;
                            n (le cid aid);
                            n (le cid bid);
                            n (le bid aid);
                            n (pnd 0 0);
                            n (pnd 0 1);
                            n (pnd 0 2);
                            n (pnd 1 0);
                            n (pnd 1 1);
                            n (pnd 1 2);
                            n (pnd 2 0);
                            n (pnd 2 1);
                            (pnd 2 2);
                            eq (nid 0) (int_to_id 0);
                            ne (nid 0) (int_to_id 1);
                            ne (nid 0) (int_to_id 2);
                            ne (nid 1) (int_to_id 0);
                            eq (nid 1) (int_to_id 1);
                            ne (nid 1) (int_to_id 2);
                            ne (nid 2) (int_to_id 0);
                            ne (nid 2) (int_to_id 1);
                            eq (nid 2) (int_to_id 2);
                            n (btw 0 0 0);
                            n (btw 0 0 1);
                            n (btw 0 0 2);
                            n (btw 0 1 0);
                            n (btw 0 1 1);
                            btw 0 1 2;
                            n (btw 0 2 0);
                            n (btw 0 2 1);
                            n (btw 0 2 2);
                          ]
                        )))))))

let makeUniversalInvariantExcludingSubstructure
      md
      (infos : Model.TypeInfos)
      (env : Model.Environment) =
    let vars : Map<string, List<VarDecl> > =
          Map.map (fun name -> fun sz ->
            List.map (fun i ->
              let tydecl = List.find (fun (typeDecl : TypeDecl) -> (typeDecl.Name = name)) md.Types
              let ty : Type =
                  match tydecl.Infos with
                    | UninterpretedTypeDecl -> Uninterpreted tydecl.Name
                    | EnumeratedTypeDecl _ -> failwith "Enumerated not implement for this func" //Enumerated tydecl.Name

              let varDecl: VarDecl = {
                Name = name + "." + i.ToString();
                Type = ty;
                Representation = { DisplayName = None; Flags = Set.empty };
               }
              varDecl
            ) [ 0 .. sz ]
          ) infos

    let rec all_pairs (vars : VarDecl list) : (VarDecl * VarDecl) list =
          match vars with
          | [] -> []
          | [x] -> []
          | x::xs -> List.append (List.map (fun y -> (x,y)) xs) (all_pairs xs)
    let not_equal_preds (vars : VarDecl list) =
          List.map (fun (v1 : VarDecl, v2 : VarDecl) ->
            ValueNot (ValueEqual (ValueVar v1.Name, ValueVar v2.Name))
          ) (all_pairs vars)
    let all_ne_preds = List.concat (List.map (fun (_, vars) -> not_equal_preds vars) (Map.toList vars))

    let facts_list = (Map.toList env.f)
    (* XXX super hack *)
    let facts_list = List.filter (fun ((fun_name,_), _) -> fun_name <> "node.<") facts_list
    let fn_preds =
          List.map (fun ((fun_name : string, args : ConstValue list), output : ConstValue) ->
            let cToVar a =
                  match a with
                    | ConstInt (sort_name, arg_value) ->
                        ValueVar ((Map.find sort_name vars).[arg_value].Name)
                    | _ -> ValueConst a

            let fn_expr = ValueFun (fun_name, List.map (fun arg ->
                    cToVar arg
                  ) args)
            let o = cToVar output
            ValueEqual (fn_expr, o)
          ) facts_list

    let all_preds = List.append all_ne_preds fn_preds
    let disj = AST.or_list (List.map ValueNot all_preds)
    let all_vars : List<VarDecl> = List.concat (List.map (fun (_,vs) -> vs) (Map.toList vars))
    let full = List.foldBack (fun v -> fun expr -> ValueForall (v, expr)) all_vars disj

    full

let do_check init_actions md decls build_mmd manual verbose =
    let main_module = ""
    let possible_actions = List.filter (fun (prov,_) -> prov = main_module) md.Exports
    let possible_actions = List.map (fun (_,str) -> str) possible_actions

    // Build minimal ASTs
    let action_mmds = List.fold (fun acc action -> Map.add action (build_mmd action) acc) Map.empty possible_actions

    let main_mmd : MinimalAST.ModuleDecl<Model.TypeInfos, Model.Environment> = { (snd (List.head (Map.toList action_mmds))) with MinimalAST.Actions = List.concat (List.map (fun (_,mmd:MinimalAST.ModuleDecl<Model.TypeInfos,Model.Environment>) -> mmd.Actions) (List.append (Map.toList action_mmds) init_actions)) }

    let inv =
          TwoState.and_list (List.map (fun (invdecl : MinimalAST.InvariantDecl) ->
            snd (WPR.minimal_val2z3_val main_mmd invdecl.Formula)
          ) main_mmd.Invariants)

    if not (TwoState.is_good_at_init main_mmd init_actions inv) then
      printfn "not valid at init"
    else
      let formulas =
          List.mapi (fun idx -> fun (invdecl : MinimalAST.InvariantDecl) ->
            (idx, invdecl.Formula)
          ) main_mmd.Invariants
      let counterexample =
          Solver.find_counterexample md action_mmds formulas

      if Option.isSome counterexample then
        printfn "non-inductive"
      else
        printfn "inductive"
 

let repeatedly_construct_universals init_actions md decls build_mmd manual verbose =
    // Choose the action to analyze
    printfn "Please enter the name of the module containing the actions to analyze:"
    let main_module = Console.ReadLine ()
    let possible_actions = List.filter (fun (prov,_) -> prov = main_module) md.Exports
    let possible_actions = List.map (fun (_,str) -> str) possible_actions

    // Build minimal ASTs
    let action_mmds = List.fold (fun acc action -> Map.add action (build_mmd action) acc) Map.empty possible_actions

    let main_mmd : MinimalAST.ModuleDecl<Model.TypeInfos, Model.Environment> = { (snd (List.head (Map.toList action_mmds))) with MinimalAST.Actions = List.concat (List.map (fun (_,mmd:MinimalAST.ModuleDecl<Model.TypeInfos,Model.Environment>) -> mmd.Actions) (List.append (Map.toList action_mmds) init_actions)) }

    //List.iter (fun (inv : InvariantDecl) -> printfn "module is '%s'" inv.Module) md.Invariants

    let invariants_to_min (invs : List<AST.InvariantDecl>) : List<MinimalAST.InvariantDecl> =
        List.map (fun (inv : InvariantDecl) ->
          {MinimalAST.Module = inv.Module; Formula = MinimalAST.value2minimal md inv.Formula}
        ) invs
    
    let invariants_ref = ref md.Invariants
    let make_counterexample () =
          let md = AST.set_invariants md !invariants_ref
          let action_mmds = Map.map (fun _ -> fun mmd -> MinimalAST.set_invariants mmd (invariants_to_min !invariants_ref)) action_mmds
          if manual
          then manual_counterexample md decls possible_actions action_mmds verbose
          else auto_counterexample md decls main_module action_mmds
    let counterexample_ref = ref (make_counterexample())

    while Option.isSome !counterexample_ref do
        let counterexample  = Option.get !counterexample_ref

        let md = AST.set_invariants md !invariants_ref
        let action_mmds = Map.map (fun _ -> fun mmd -> MinimalAST.set_invariants mmd (invariants_to_min !invariants_ref)) action_mmds
        let main_mmd = MinimalAST.set_invariants main_mmd (invariants_to_min !invariants_ref)

        let (action_name, infos, env, cs, formula, tr) = counterexample
        //printfn "%A" infos
        //printfn "%A" env
        let new_inv = makeUniversalInvariantExcludingSubstructure md infos env
        let z3_new_inv = snd (WPR.minimal_val2z3_val main_mmd (MinimalAST.value2minimal md new_inv))

        let z3_new_inv_min = AwesomeMinimize.normal_minimize md main_mmd decls init_actions z3_new_inv
        let new_inv_min = MinimalAST.value2ast (WPR.z3value_to_value z3_new_inv_min)

        printfn "Adding invariant: %s" (Printer.z3value_to_string z3_new_inv_min)
        invariants_ref := List.append !invariants_ref [{InvariantDecl.Module = ""; Formula = new_inv_min}]

        counterexample_ref := make_counterexample()

    printfn "done!"


let do_analysis1 init_actions md decls build_mmd manual verbose =
    // Choose the action to analyze
    printfn "Please enter the name of the module containing the actions to analyze:"
    let main_module = Console.ReadLine ()
    let possible_actions = List.filter (fun (prov,_) -> prov = main_module) md.Exports
    let possible_actions = List.map (fun (_,str) -> str) possible_actions

    if not (List.isEmpty possible_actions)
    then
        // Build minimal ASTs
        let mmds = List.fold (fun acc action -> Map.add action (build_mmd action) acc) Map.empty possible_actions

        let main_mmd = { (snd (List.head (Map.toList mmds))) with MinimalAST.Actions = List.concat (List.map (fun (_,mmd:MinimalAST.ModuleDecl<Model.TypeInfos,Model.Environment>) -> mmd.Actions) (List.append (Map.toList mmds) init_actions)) }

        // Let's go!

        let counterexample =
            if manual
            then manual_counterexample md decls possible_actions mmds verbose
            else auto_counterexample md decls main_module mmds

        match counterexample with
        | None -> ()
        | Some (action_name, infos, env, cs, formula, tr) ->
            printfn "invariant violated: %s" (Printer.mvalue_to_string decls formula)

            let mmd = Map.find action_name mmds

            let wpr = WPR.wpr_for_action mmd (Solver.minimal_formula_to_z3 mmd formula) action_name false
            let wpr = WPR.simplify_z3_value wpr

            //let wpr = testing
            //TwoState.is_k_invariant main_mmd init_actions 3 wpr

            printfn "wpr: %s" (Printer.z3value_to_string wpr)

            let mini = AwesomeMinimize.minimize md main_mmd decls init_actions wpr
            printfn "minimized: %s" (Printer.z3value_to_string mini)


let do_analysis init_actions md decls build_mmd manual verbose =
    // Choose the action to analyze
    printfn "Please enter the name of the module containing the actions to analyze:"
    let main_module = Console.ReadLine ()
    let possible_actions = List.filter (fun (prov,_) -> prov = main_module) md.Exports
    let possible_actions = List.map (fun (_,str) -> str) possible_actions

    if not (List.isEmpty possible_actions)
    then
        // Build minimal ASTs
        let mmds = List.fold (fun acc action -> Map.add action (build_mmd action) acc) Map.empty possible_actions

        // Let's go!

        let counterexample =
            if manual
            then manual_counterexample md decls possible_actions mmds verbose
            else auto_counterexample md decls main_module mmds

        match counterexample with
        | None -> ()
        | Some (name, infos, env, cs, formula, tr) ->
            Printer.print_model infos env

            let mmd = Map.find name mmds
            let (b,finished_exec,(m,um,ad)) =
                analyse_example_ending mmd decls infos tr formula
            if b then failwith "Invalid counterexample!"

            printfn "Going back through the action..."
            let (m,um,ad) = Marking.marks_before_statement mmd decls infos true false tr (m,um,ad)
            let (m,um) = (Marking.remove_all_var_marks m, Marking.remove_all_var_marks um)
            if verbose
            then
                printfn "%A" m
                printfn "%A" um
                printfn "%A" ad
            let common_cvs = Formula.concrete_values_of_marks env m

            // Printing intermediate result
            let f = Formula.generate_invariant env common_cvs (Solver.simplify_marks md mmd env m (Marking.empty_marks)) []
            let f = Formula.simplify_value f
            printfn "%s" (Printer.value_to_string decls f 0)
            printfn ""

            let allowed_paths = ref []
            if ad.md
            then
                printfn "This invariant may be too strong!"
                printfn "(Some model-dependent marks have been ignored)"
                printfn "Would you like to weaken the invariant with an allowed execution? (y/n)"
                let answer = ref (Console.ReadLine())
                let only_terminating_exec = ref true
                while !answer = "y" do

                    let allowed_path_opt =
                        if manual
                        then manual_allowed_path md decls env cs m um
                        else auto_allowed_path md mmd env formula name m (Map.toList mmds) common_cvs (!allowed_paths) (!only_terminating_exec)

                    match allowed_path_opt with
                    | Some (infos_allowed, env_allowed) ->
                        let args_decl = (MinimalAST.find_action mmd name).Args
                        let tr_allowed = TInterpreter.trace_action mmd infos_allowed env_allowed name (List.map (fun (d:VarDecl) -> MinimalAST.ValueVar d.Name) args_decl) AST.impossible_var_factor

                        let (b_al,_,(m_al,um_al,ad_al)) =
                            analyse_example_ending mmd decls infos_allowed tr_allowed formula

                        if b_al
                        then
                            let (m_al,_,ad_al) = Marking.marks_before_statement mmd decls infos_allowed finished_exec true tr_allowed (m_al,um_al,ad_al)
                            let m_al = Marking.remove_all_var_marks m_al
                            if ad_al.md
                            then printfn "Warning: Some marks still are model-dependent! Generated invariant could be weaker than expected."

                            // Printing
                            let f_al = Formula.generate_semi_generalized_formula common_cvs (0,Map.empty) env_allowed (Solver.simplify_marks md mmd env_allowed m_al m)
                            let f_al = Formula.simplify_value f_al
                            printfn "%s" (Printer.value_to_string decls f_al 0)

                            // Minimization (optional)
                            printfn "Try to minimize this existential part now (can weaken the final invariant)? (n:no/y:yes)"
                            let m_al =
                                let line = Console.ReadLine ()
                                if line = "y"
                                then
                                    let m_al = Solver.wpr_based_minimization_existential_part md mmd infos env (Map.toList mmds) formula m common_cvs env_allowed m_al
                                    let f_al = Formula.generate_semi_generalized_formula common_cvs (0,Map.empty) env_allowed (Solver.simplify_marks md mmd env_allowed m_al m)
                                    let f_al = Formula.simplify_value f_al
                                    printfn "%s" (Printer.value_to_string decls f_al 0)
                                    m_al
                                else m_al

                            allowed_paths := (m_al,env_allowed)::(!allowed_paths)
                        else printfn "ERROR: Illegal execution!"
                    | None ->
                        printfn "No more allowed execution found!"
                        if !only_terminating_exec = true
                        then
                            printfn "Extending the search domain to non-terminating runs..."
                            only_terminating_exec := false
        
                    printfn "Would you like to weaken the invariant with an allowed execution? (y/n)"
                    answer := Console.ReadLine()
            else
                printfn "These conditions are sufficient to break the invariant!"

            printfn "Minimize universal part? (n:no/s:safe/h:hard/[0-9]:sbv)"
            let m =
                let line = Console.ReadLine ()
                if line = "h"
                then Solver.wpr_based_minimization md mmd infos env name (Map.toList mmds) formula m common_cvs (!allowed_paths) true
                else if line = "s"
                then Solver.wpr_based_minimization md mmd infos env name (Map.toList mmds) formula m common_cvs (!allowed_paths) false
                else if line = "n"
                then m
                else
                    let boundary = int(Convert.ToUInt32 (line))
                    Solver.sbv_based_minimization md mmd infos env (Map.toList mmds) init_actions m common_cvs (!allowed_paths) boundary
            let m = Solver.simplify_marks md mmd env m (Marking.empty_marks)

            if List.length (!allowed_paths) > 0
            then
                printfn "Minimize existential parts? (n:no/y:yes)"
                if Console.ReadLine () = "y"
                then
                    let allowed_paths' = List.map (fun (m_al,env_al) -> (Solver.wpr_based_minimization_existential_part md mmd infos env (Map.toList mmds) formula m common_cvs env_al m_al,env_al)) (!allowed_paths)
                    allowed_paths := allowed_paths'
                let allowed_paths' = List.map (fun (m_al,env_al) -> (Solver.simplify_marks md mmd env_al m_al m,env_al)) (!allowed_paths)
                allowed_paths := allowed_paths'

            let f = Formula.generate_invariant env common_cvs m (!allowed_paths)
            let f = Formula.simplify_value f
            printfn "\nInvariant to add:"
            printfn "%s" (Printer.value_to_string decls f 0)
            ignore (Console.ReadLine())

[<EntryPoint>]
let main argv =

    let verbose = Array.contains "-v" argv
    let manual = Array.contains "-m" argv
    let check = Array.contains "--check" argv

    let filename = 
        match Array.tryLast argv with
        | None -> ""
        | Some str ->
            if str.EndsWith(".ivy") || str.EndsWith(".mik")
            then str else ""

    let (md:ModuleDecl) =
        if filename = ""
        then
            printfn "Loading hardcoded test module 'queue'..."
            TestModule.Queue.queue_module
        else
            //printfn "Parsing module..."
            let args = Config.parser_args.Replace("%IN%", "\"" + filename + "\"").Replace("%OUT%", "\"" + Config.parser_output_path + "\"").Replace("%ERR%", "\"" + Config.parser_error_path + "\"")
            System.IO.File.Delete(Config.parser_output_path)
            System.IO.File.Delete(Config.parser_error_path)
            System.Diagnostics.Process.Start(Config.parser_cmd, args).WaitForExit()
            let err =
                try System.IO.File.ReadAllText(Config.parser_error_path)
                with :? System.IO.FileNotFoundException -> ""
            if err <> ""
            then
                printfn "Parser error: %s" err
                ignore (Console.ReadLine())
                failwith "Parser error!"
            else
                let content = System.IO.File.ReadAllText(Config.parser_output_path)
                let parsed_elts = ParserAST.deserialize content
                //printfn "Converting parsed AST..."
                ParserAST.ivy_elements_to_ast_module filename parsed_elts

    // Remove unwanted implementations from the module decl
    //printfn "Please enter the names of the concrete modules to ignore:"
    //let str = read_until_line_jump ()
    //let banned_modules = str.Split([|Environment.NewLine|], StringSplitOptions.RemoveEmptyEntries)
    let banned_modules = []
    let md = AST.exclude_from_module md (Seq.toList banned_modules)
    let decls = Model.declarations_of_module md

    let build_mmd action =
        Determinization.determinize_action (MinimalAST.module2minimal md action) action
    // Compute `init` actions
    let all_actions =
        List.fold (fun acc (a:AST.ActionDecl) -> let (name,_) = AST.decompose_action_name a.Name in Set.add name acc) Set.empty md.Actions
    let init_actions = Set.filter (fun str -> let (_,name) = AST.decompose_name str in name = "init") all_actions
    let action_is_child str1 str2 =
        let (mod1,_) = AST.decompose_name str1
        let (mod2,_) = AST.decompose_name str2
        AST.has_base_name mod1 mod2
    let init_actions_cmp str1 str2 =
        if str1=str2 then 0
        else if action_is_child str1 str2 then -1
        else if action_is_child str2 str1 then 1
        else 0
    let init_actions = List.sortWith init_actions_cmp (Set.toList init_actions)
    let init_actions = List.map (fun str -> (str,build_mmd str)) init_actions

    if check then
      // just check if it's invariant, don't try to do anything else
      do_check init_actions md decls build_mmd manual verbose
    else
      repeatedly_construct_universals init_actions md decls build_mmd manual verbose
      //do_analysis1 init_actions md decls build_mmd manual verbose

      //while true do
      //    do_analysis init_actions md decls build_mmd manual verbose

    0

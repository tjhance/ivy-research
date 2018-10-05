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

let marks_to_string md (env:Model.Environment) (m:Marking.Marks) =
  let res = Set.fold (fun acc v -> sprintf "%s%s\n" acc (Printer.varmark_to_string md env v)) "" m.v
  let res = Set.fold (fun acc f -> sprintf "%s%s\n" acc (Printer.funmark_to_string md env f)) res m.f
  res
    
let manual_allowed_path (md:ModuleDecl) (env:Model.Environment) cs m um =
    printfn "Please modify some constraints on the environment to change the final formula value."
    printfn ""
    printfn "Constraints you can't change:"
    printfn "%s" (marks_to_string md env m)
    printfn ""
    printfn "Constraints you should change (at least one):"
    printfn "%s" (marks_to_string md env um)

    printfn ""
    let str = read_until_line_jump ()
    printfn "Loading constraints..."
    let cs' = ConstraintsParser.parse_from_str md str
    printfn "Building new environment..."
    let (infos_allowed, env_allowed) = Model.constraints_to_env md (cs@cs')
    printfn "Computing..."
    Some (infos_allowed, { env_allowed with v=env.v }) // We keep the same args as before

let auto_allowed_path (md:ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (env:Model.Environment) formula
    (action_name:string) (m:Marking.Marks) prev_allowed only_terminating_run =
    Solver.find_allowed_execution md mmd env formula (MinimalAST.find_action mmd action_name) m prev_allowed only_terminating_run


// ----- MAIN -----

let analyse_example_ending mmd infos tr formula =
    let env' = Trace.final_env tr
    if Trace.is_fully_executed tr
    then
        let (b,cfgs) = Marking.marks_for_value mmd infos env' Set.empty formula
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

let do_check md mmd verbose =
    let inv =
          TwoState.and_list (List.map (fun (invdecl : MinimalAST.InvariantDecl) ->
            snd (WPR.minimal_val2z3_val mmd invdecl.Formula)
          ) mmd.Invariants)

    if not (TwoState.is_good_at_init mmd inv) then
      printfn "not valid at init"
    else
      let counterexample = Solver.find_counterexample md mmd

      if Option.isSome counterexample then
        printfn "non-inductive"
      else
        printfn "inductive"
 

let repeatedly_construct_universals md mmd verbose =
    let invariants_to_min (invs : List<AST.InvariantDecl>) : List<MinimalAST.InvariantDecl> =
        List.map (fun (inv : InvariantDecl) ->
          {MinimalAST.Module = inv.Module; Formula = MinimalAST.value2minimal md inv.Formula}
        ) invs
    
    let invariants_ref = ref md.Invariants
    let make_counterexample () =
          let md = AST.set_invariants md !invariants_ref
          let mmd = MinimalAST.set_invariants mmd (invariants_to_min !invariants_ref)
          Solver.find_counterexample md mmd
    let counterexample_ref = ref (make_counterexample())

    while Option.isSome !counterexample_ref do
        let counterexample  = Option.get !counterexample_ref

        let md = AST.set_invariants md !invariants_ref
        let mmd = MinimalAST.set_invariants mmd (invariants_to_min !invariants_ref)

        let (action_name, infos, env, cs, formula, tr) = counterexample
        //printfn "%A" infos
        //printfn "%A" env
        let new_inv = makeUniversalInvariantExcludingSubstructure md infos env
        let z3_new_inv = snd (WPR.minimal_val2z3_val mmd (MinimalAST.value2minimal md new_inv))

        let z3_new_inv_min = AwesomeMinimize.normal_minimize md mmd z3_new_inv
        let new_inv_min = MinimalAST.value2ast (WPR.z3value_to_value z3_new_inv_min)

        printfn "Adding invariant: %s" (Printer.z3value_to_string z3_new_inv_min)
        invariants_ref := List.append !invariants_ref [{InvariantDecl.Module = ""; Formula = new_inv_min}]

        counterexample_ref := make_counterexample()

    printfn "done!"


let do_analysis1 md mmd verbose =
    let counterexample = Solver.find_counterexample md mmd

    match counterexample with
    | None -> ()
    | Some (action_name, infos, env, cs, formula, tr) ->
        printfn "invariant violated: %s" (Printer.mvalue_to_string md formula)

        let action = MinimalAST.find_action mmd action_name
        let wpr = WPR.wpr_for_action mmd (Solver.minimal_formula_to_z3 mmd formula) action false
        let wpr = WPR.simplify_z3_value wpr

        //let wpr = testing
        //TwoState.is_k_invariant mmd init_actions 3 wpr

        printfn "wpr: %s" (Printer.z3value_to_string wpr)

        let mini = AwesomeMinimize.minimize md mmd wpr
        printfn "minimized: %s" (Printer.z3value_to_string mini)


let do_analysis md mmd manual verbose =
    // Let's go!

    let counterexample = Solver.find_counterexample md mmd

    match counterexample with
    | None -> ()
    | Some (name, infos, env, cs, formula, tr) ->
        Printer.print_model infos env

        let (b,finished_exec,(m,um,ad)) =
            analyse_example_ending mmd infos tr formula
        if b then failwith "Invalid counterexample!"

        printfn "Going back through the action..."
        let (m,um,ad) = Marking.marks_before_statement mmd infos true false tr (m,um,ad)
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
        printfn "%s" (Printer.value_to_string md f 0)
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
                    then manual_allowed_path md env cs m um
                    else auto_allowed_path md mmd env formula name m common_cvs (!allowed_paths) (!only_terminating_exec)

                match allowed_path_opt with
                | Some (infos_allowed, env_allowed) ->
                    let args_decl = (MinimalAST.find_action mmd name).Args
                    let tr_allowed = TInterpreter.trace_action mmd infos_allowed env_allowed name (List.map (fun (d:VarDecl) -> MinimalAST.ValueVar d.Name) args_decl) AST.impossible_var_factor

                    let (b_al,_,(m_al,um_al,ad_al)) =
                        analyse_example_ending mmd infos_allowed tr_allowed formula

                    if b_al
                    then
                        let (m_al,_,ad_al) = Marking.marks_before_statement mmd infos_allowed finished_exec true tr_allowed (m_al,um_al,ad_al)
                        let m_al = Marking.remove_all_var_marks m_al
                        if ad_al.md
                        then printfn "Warning: Some marks still are model-dependent! Generated invariant could be weaker than expected."

                        // Printing
                        let f_al = Formula.generate_semi_generalized_formula common_cvs (0,Map.empty) env_allowed (Solver.simplify_marks md mmd env_allowed m_al m)
                        let f_al = Formula.simplify_value f_al
                        printfn "%s" (Printer.value_to_string md f_al 0)

                        // Minimization (optional)
                        printfn "Try to minimize this existential part now (can weaken the final invariant)? (n:no/y:yes)"
                        let m_al =
                            let line = Console.ReadLine ()
                            if line = "y"
                            then
                                let m_al = Solver.wpr_based_minimization_existential_part md mmd infos env formula m common_cvs env_allowed m_al
                                let f_al = Formula.generate_semi_generalized_formula common_cvs (0,Map.empty) env_allowed (Solver.simplify_marks md mmd env_allowed m_al m)
                                let f_al = Formula.simplify_value f_al
                                printfn "%s" (Printer.value_to_string md f_al 0)
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
            then Solver.wpr_based_minimization md mmd infos env (MinimalAST.find_action mmd name) formula m common_cvs (!allowed_paths) true
            else if line = "s"
            then Solver.wpr_based_minimization md mmd infos env (MinimalAST.find_action mmd name) formula m common_cvs (!allowed_paths) false
            else if line = "n"
            then m
            else
                let boundary = int(Convert.ToUInt32 (line))
                Solver.sbv_based_minimization md mmd infos env m common_cvs (!allowed_paths) boundary
        let m = Solver.simplify_marks md mmd env m (Marking.empty_marks)

        if List.length (!allowed_paths) > 0
        then
            printfn "Minimize existential parts? (n:no/y:yes)"
            if Console.ReadLine () = "y"
            then
                let allowed_paths' = List.map (fun (m_al,env_al) -> (Solver.wpr_based_minimization_existential_part md mmd infos env formula m common_cvs env_al m_al,env_al)) (!allowed_paths)
                allowed_paths := allowed_paths'
            let allowed_paths' = List.map (fun (m_al,env_al) -> (Solver.simplify_marks md mmd env_al m_al m,env_al)) (!allowed_paths)
            allowed_paths := allowed_paths'

        let f = Formula.generate_invariant env common_cvs m (!allowed_paths)
        let f = Formula.simplify_value f
        printfn "\nInvariant to add:"
        printfn "%s" (Printer.value_to_string md f 0)
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

    let main_module = ""
    let possible_actions = List.filter (fun (prov,_) -> prov = main_module) md.Exports
    let possible_actions = List.map (fun (_,str) -> str) possible_actions

    // Build minimal ASTs
    let action_mmds = List.fold (fun acc action -> Map.add action (build_mmd action) acc) Map.empty possible_actions

    // XXX the way of constructing this is weird and roundabout
    let get_actions x = List.concat (List.map (fun (_,mmd:MinimalAST.ModuleDecl<Model.TypeInfos,Model.Environment>) -> mmd.Actions) x)
    let mmd : MinimalAST.ModuleDecl<Model.TypeInfos, Model.Environment> =
      {
        (snd (List.head (Map.toList action_mmds)))
        with
          MinimalAST.Actions = get_actions (Map.toList action_mmds)
          InitActions = get_actions init_actions
      }

    if check then
      // just check if it's invariant, don't try to do anything else
      do_check md mmd verbose
    else
      repeatedly_construct_universals md mmd verbose
      //do_analysis1 init_actions md decls build_mmd manual verbose

      //while true do
      //    do_analysis init_actions md decls build_mmd manual verbose

    0

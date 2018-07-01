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

let parser_cmd = "lin"
let parser_args = "parser.native all %IN% %OUT% %ERR%"
let parser_output_path = "parser.out"
let parser_error_path = "parser.err"

// ----- MANUAL MODE -----

let manual_counterexample (md:ModuleDecl) decls verbose =
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

    printfn "Please enter the name of the (concrete) action to execute:"
    let name = Console.ReadLine()
    let args =
        List.map
            (
                fun vd ->
                    printfn "Please enter next arg:"
                    match vd.Type with
                    | Void -> ConstVoid
                    | Bool -> ConstBool (Convert.ToBoolean (Console.ReadLine()))
                    | Uninterpreted str -> ConstInt (str, Convert.ToInt32 (Console.ReadLine()))
            )
            (find_action md name "").Args

    let mmd = MinimalAST.module2minimal md name

    printfn "Executing..."
    let tr = TInterpreter.trace_action mmd infos env name (List.map (fun cv -> MinimalAST.ValueConst cv) args) AST.impossible_var_factor
    let env' = Trace.final_env tr
    if verbose
    then
        printfn "%A" env'

    if Trace.is_fully_executed tr
    then
        printfn "Please enter the index of the invariant to analyze:"

        List.iteri
            (
                fun i v ->
                    let mv = MinimalAST.value2minimal md v
                    match Interpreter.evaluate_value mmd infos env' mv with
                    | ConstBool true -> Console.ForegroundColor <- ConsoleColor.Green
                    | ConstBool false -> Console.ForegroundColor <- ConsoleColor.Red
                    | _ -> Console.ResetColor()
                    printfn "%i. %s" i (Printer.value_to_string decls v 0)
            ) md.Invariants
        Console.ResetColor()

        let nb = Convert.ToInt32 (Console.ReadLine())
        let formula = List.item nb md.Invariants
        let formula = MinimalAST.value2minimal md formula
        (mmd, name, args, infos, env, cs, formula, tr)
    else
        (mmd, name, args, infos, env, cs, MinimalAST.ValueConst (ConstBool true), tr)
    
let manual_allowed_path (md:ModuleDecl) decls env cs m um' =
    printfn "Please modify some constraints on the environment to change the final formula value."
    printfn ""
    printfn "Constraints you can't change:"
    printfn "%s" (Printer.marks_to_string decls env m)
    printfn ""
    printfn "Constraints you should change (at least one):"
    printfn "%s" (Printer.marks_to_string decls env um')

    printfn ""
    let str = read_until_line_jump ()
    printfn "Loading constraints..."
    let cs' = ConstraintsParser.parse_from_str md str
    printfn "Building new environment..."
    let (infos_allowed, env_allowed) = Model.constraints_to_env md (cs@cs')
    printfn "Computing..."
    Some (infos_allowed, env_allowed)

// ----- AUTO MODE -----

let auto_counterexample (md:ModuleDecl) decls verbose =

    printfn "Enter the name of the action:"
    let action = Console.ReadLine()
    let mmd = MinimalAST.module2minimal md action

    let counterexample = ref None
    let first_loop = ref true

    while (!counterexample) = None do

        let formula =
            if !first_loop
            then
                first_loop := false
                printfn "Searching assertions fail..."
                MinimalAST.ValueConst (ConstBool true)
            else
                printfn "Select the conjecture to test:"
                List.iteri (fun i v -> printfn "%i. %s" i (Printer.value_to_string decls v 0)) md.Invariants
                let nb = Convert.ToInt32 (Console.ReadLine())
                let formula = List.item nb md.Invariants
                MinimalAST.value2minimal md formula

        let z3formula = WPR.z3val2deterministic_formula (WPR.minimal_val2z3_val mmd formula) false
        let wpr = WPR.wpr_for_action mmd z3formula action false
        if verbose then printfn "%A" wpr

        let conjectures = WPR.conjunction_of (WPR.conjectures_to_z3values mmd mmd.Invariants)
        let axioms = WPR.conjunction_of (WPR.conjectures_to_z3values mmd mmd.Axioms)
    
        let is_inductive_v = WPR.Z3And (WPR.Z3And (conjectures, axioms), WPR.Z3Not wpr)
        let z3ctx = Z3Utils.build_context mmd
        let (z3lvars, z3concrete_map) = Z3Utils.declare_lvars mmd action z3ctx is_inductive_v
        let z3e = Z3Utils.build_value z3ctx z3lvars is_inductive_v
        
        counterexample :=
            match Z3Utils.check z3ctx z3e with
            | None -> None
            | Some m ->
                let action_args = (MinimalAST.find_action mmd action).Args
                let (infos, env, args) = Z3Utils.z3model_to_ast_model md z3ctx action_args z3lvars z3concrete_map m
                let args = List.map (fun (d:VarDecl) -> Map.find d.Name args) action_args
                Some (formula, args, infos, env)

    match !counterexample with
    | None -> failwith "No counterexample found!"
    | Some (formula, args, infos, env) ->
        let tr = TInterpreter.trace_action mmd infos env action (List.map (fun cv -> MinimalAST.ValueConst cv) args) AST.impossible_var_factor
        (mmd, action, args, infos, env, [], formula, tr)

let auto_allowed_path (md:ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) _ (env:Model.Environment) formula
    action (m:Synthesis.Marks) prev_allowed =

    // 1. Marked constraints
    let add_var_constraint cs str =
        let cv = Map.find str env.v
        ValueAnd (cs, ValueEqual (ValueVar str, ValueConst cv))
    let cs = Set.fold add_var_constraint (ValueConst (ConstBool true)) m.v
    let add_fun_constraint cs (str, cvs) =
        let cv = Map.find (str, cvs) env.f
        let vs = List.map (fun cv -> ValueConst cv) cvs
        ValueAnd (cs, ValueEqual (ValueFun (str, vs), ValueConst cv))
    let cs = Set.fold add_fun_constraint cs m.f
    let add_diff_constraint cs (cv1, cv2) =
        ValueAnd (cs, ValueNot (ValueEqual (ValueConst cv1, ValueConst cv2)))
    let cs = Set.fold add_diff_constraint cs m.d
    let cs = MinimalAST.value2minimal md cs
    let cs = WPR.z3val2deterministic_formula (WPR.minimal_val2z3_val mmd cs) false

    // 2. NOT Previous semi-generalized allowed examples
    let f = Formula.formula_from_marks env m prev_allowed true
    let f = ValueNot f
    let f = MinimalAST.value2minimal md f
    let f = WPR.z3val2deterministic_formula (WPR.minimal_val2z3_val mmd f) false

    // 3. Possibly valid run: WPR & conjectures & axioms
    let z3formula = WPR.z3val2deterministic_formula (WPR.minimal_val2z3_val mmd formula) false
    let wpr = WPR.wpr_for_action mmd z3formula action true
    let conjectures = WPR.conjunction_of (WPR.conjectures_to_z3values mmd mmd.Invariants)
    let axioms = WPR.conjunction_of (WPR.conjectures_to_z3values mmd mmd.Axioms)
    let valid_run = WPR.Z3And (axioms, WPR.Z3And(conjectures, wpr))

    // All together
    let f = WPR.Z3And (cs, WPR.Z3And(f,valid_run))
    let z3ctx = Z3Utils.build_context mmd
    let (z3lvars, z3concrete_map) = Z3Utils.declare_lvars mmd action z3ctx f
    let z3e = Z3Utils.build_value z3ctx z3lvars f

    // Solve!
    match Z3Utils.check z3ctx z3e with
    | None -> None
    | Some m ->
        // This time, action args are quantified
        printfn "%s" (m.ToString()) //TMP
        // TODO: fix it (example2.set_elt)
        let (infos, env, _) = Z3Utils.z3model_to_ast_model md z3ctx [] z3lvars z3concrete_map m
        printfn "%A" (Map.filter (fun (str,_) _ -> str = "example2.dom") env.f) //TMP
        Some (infos, env)

// ----- MAIN -----

[<EntryPoint>]
let main argv =

    let verbose = Array.contains "-v" argv
    let manual = Array.contains "-m" argv

    let filename = 
        match Array.tryLast argv with
        | None -> ""
        | Some str ->
            if str.EndsWith(".ivy")
            then str else ""

    let (md:ModuleDecl) =
        if filename = ""
        then
            printfn "Loading hardcoded test module 'queue'..."
            TestModule.Queue.queue_module
        else
            printfn "Parsing module..."
            let args = parser_args.Replace("%IN%", "\"" + filename + "\"").Replace("%OUT%", "\"" + parser_output_path + "\"").Replace("%ERR%", "\"" + parser_error_path + "\"")
            System.IO.File.Delete(parser_output_path)
            System.IO.File.Delete(parser_error_path)
            System.Diagnostics.Process.Start(parser_cmd, args).WaitForExit()
            let err =
                try System.IO.File.ReadAllText(parser_error_path)
                with :? System.IO.FileNotFoundException -> ""
            if err <> ""
            then
                printfn "Parser error: %s" err
                ignore (Console.ReadLine())
                failwith "Parser error!"
            else
                let content = System.IO.File.ReadAllText(parser_output_path)
                let parsed_elts = ParserAST.deserialize content
                printfn "Converting parsed AST..."
                ParserAST.ivy_elements_to_ast_module filename parsed_elts
    let decls = Model.declarations_of_module md

    let (mmd, name, args, infos, env, cs, formula, tr) =
        if manual
        then manual_counterexample md decls verbose
        else auto_counterexample md decls verbose
    let env' = Trace.final_env tr
    let (b,(m,um,ad)) =
        if Trace.is_fully_executed tr
        then
            let (b,cfg) = Synthesis.marks_for_value mmd infos env' Set.empty formula
            (Some b, cfg)
        else (None,Synthesis.empty_config)

    printfn "Going back through the action..."
    let (m,um,ad) = Synthesis.marks_before_statement mmd infos true tr (m,um,ad)
    if verbose
    then
        printfn "%A" m
        printfn "%A" um
        printfn "%A" ad

    let m' = Formula.simplify_marks infos md.Implications decls env m
    let um' = Formula.simplify_marks infos md.Implications decls env um
    let f = Formula.formula_from_marks env m' [] false
    let f = Formula.simplify_value f
    printfn "%s" (Printer.value_to_string decls f 0)
    printfn ""

    let allowed_paths = ref []
    if ad.md
    then
        printfn "This invariant may be too strong!"
        printfn "(Some model-dependent marks have been ignored)"
        printfn "Would you like to add an allowed path to the invariant? (y/n)"
        let answer = ref (Console.ReadLine())
        while !answer = "y" do

            let allowed_path_opt =
                if manual
                then manual_allowed_path md decls env cs m um'
                else auto_allowed_path md mmd decls env formula name m (!allowed_paths)

            match allowed_path_opt with
            | Some (infos_allowed, env_allowed) ->
                let tr_allowed = TInterpreter.trace_action mmd infos_allowed env_allowed name (List.map (fun cv -> MinimalAST.ValueConst cv) args) AST.impossible_var_factor
                let env_allowed' = Trace.final_env tr_allowed

                if Trace.is_fully_executed tr_allowed
                then
                    let (b_al,(m_al,um_al,ad_al)) =
                        Synthesis.marks_for_value mmd infos_allowed env_allowed' Set.empty formula
                    if Some b_al <> b
                    then
                        let (m_al,_,ad_al) =
                            Synthesis.marks_before_statement mmd infos_allowed (b <> None) tr_allowed (m_al,um_al,ad_al)
                        if ad_al.md
                        then printfn "Warning: Some marks still are model-dependent! Generated invariant could be weaker than expected."
                        let m_al' = Synthesis.marks_union m_al m'
                        let m_al' = Formula.simplify_marks infos_allowed md.Implications decls env_allowed m_al'
                        let m_al' = Synthesis.marks_diff m_al' m'
                        allowed_paths := (m_al',env_allowed)::(!allowed_paths)
                    else printfn "ERROR: Execution has the same ending situation than before!"
                else printfn "ERROR: Allowed execution fail!"
            | None -> printfn "No more allowed path found!"
            
            printfn "Would you like to add an allowed path to the invariant? (y/n)"
            answer := Console.ReadLine()
    else
        printfn "These conditions are sufficient to satisfy/break the invariant!"

    let f =
        if not (List.isEmpty (!allowed_paths))
        then
            let f = Formula.formula_from_marks env m' (!allowed_paths) false
            Formula.simplify_value f
        else f

    printfn ""
    printfn "Invariant to add:"
    printfn "%s" (Printer.value_to_string decls f 0)
    
    ignore (Console.ReadLine())
    0

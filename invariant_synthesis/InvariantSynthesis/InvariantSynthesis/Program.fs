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

[<EntryPoint>]
let main argv =

    let verbose = Array.contains "-v" argv

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

    /////////////////////////////////////////////////////////////////

    printfn "Select the conjecture to test:"
    List.iteri (fun i v -> printfn "%i. %s" i (Printer.value_to_string decls v 0)) md.Invariants
    let nb = Convert.ToInt32 (Console.ReadLine())
    let formula = List.item nb md.Invariants
    let formula = MinimalAST.value2minimal md formula

    printfn "Enter the name of the action:"
    let action = Console.ReadLine()
    let mmd = MinimalAST.module2minimal md action
    let z3formula = WPR.z3val2deterministic_formula (WPR.minimal_val2z3_val mmd formula) false
    let wpr = WPR.wpr_for_action mmd z3formula action
    printfn "%A" wpr

    let conjectures = WPR.conjunction_of (WPR.conjectures_to_z3values mmd mmd.Invariants)
    let axioms = WPR.conjunction_of (WPR.conjectures_to_z3values mmd mmd.Axioms)
    
    let is_inductive_v = WPR.Z3And (WPR.Z3And (conjectures, axioms), WPR.Z3Not wpr)
    let z3ctx = Z3Utils.build_context mmd
    let z3lvars = Z3Utils.declare_lvars mmd action z3ctx is_inductive_v
    let z3e = Z3Utils.build_value mmd z3ctx z3lvars is_inductive_v
    match Z3Utils.check z3ctx z3e with
    | None -> printfn "Invariant is inductive!"
    | Some m ->
        printfn "Invariant is not inductive!"
        printfn "Model: %s" (m.ToString())
        ignore (Z3Utils.z3model_to_ast_model md z3ctx z3lvars m)

    /////////////////////////////////////////////////////////////////
        
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
            (find_action md name false).Args

    let mmd = MinimalAST.module2minimal md name
    printfn "Executing..."
    let tr = TInterpreter.trace_action mmd infos env name (List.map (fun cv -> MinimalAST.ValueConst cv) args) AST.impossible_var_factor
    let env' = Trace.final_env tr
    if verbose
    then
        printfn "%A" env'

    let ((m,um,ad),formula,b) =
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

            printfn "Generating marks for the formula (post execution)..."
            let (b,(m,um,ad)) = Synthesis.marks_for_value mmd infos env' Set.empty formula
            if verbose
            then
                printfn "%A" b
                printfn "%A" m
                printfn "%A" um
                printfn "%A" ad
            ((m,um,ad), Some formula, b)
        else
            printfn "Assertion failed... No invariant to analyze."
            printfn "Analyzing the cause of failure."
            (Synthesis.empty_config, None, ConstVoid)

    printfn "Going back through the action..."
    let (m,um,ad) = Synthesis.marks_before_statement mmd infos true tr (m,um,ad)
    if verbose
    then
        printfn "%A" m
        printfn "%A" um
        printfn "%A" ad

    let m' = Formula.simplify_marks infos md.Implications decls env m
    let um' = Formula.simplify_marks infos md.Implications decls env um
    let f = Formula.formula_from_marks env m' []
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
            let tr_allowed = TInterpreter.trace_action mmd infos_allowed env_allowed name (List.map (fun cv -> MinimalAST.ValueConst cv) args) AST.impossible_var_factor
            let env_allowed' = Trace.final_env tr_allowed
            match formula with
            | None ->
                if Trace.is_fully_executed tr_allowed
                then
                    let (m_al,_,ad_al) =
                        Synthesis.marks_before_statement mmd infos_allowed false tr_allowed Synthesis.empty_config
                    if ad_al.md
                    then printfn "Warning: Some marks still are model-dependent! Generated invariant could be weaker than expected."
                    let m_al' = Synthesis.marks_union m_al m'
                    let m_al' = Formula.simplify_marks infos_allowed md.Implications decls env_allowed m_al'
                    let m_al' = Synthesis.marks_diff m_al' m'
                    allowed_paths := (m_al',env_allowed)::(!allowed_paths)
                else printfn "ERROR: Execution still fail!"
            | Some formula ->
                let (b_al,(m_al,um_al,ad_al)) =
                    Synthesis.marks_for_value mmd infos_allowed env_allowed' Set.empty formula
                if b_al <> b
                then
                    let (m_al,_,ad_al) =
                        Synthesis.marks_before_statement mmd infos_allowed true tr_allowed (m_al,um_al,ad_al)
                    if ad_al.md
                    then printfn "Warning: Some marks still are model-dependent! Generated invariant could be weaker than expected."
                    let m_al' = Synthesis.marks_union m_al m'
                    let m_al' = Formula.simplify_marks infos_allowed md.Implications decls env_allowed m_al'
                    let m_al' = Synthesis.marks_diff m_al' m'
                    allowed_paths := (m_al',env_allowed)::(!allowed_paths)
                else printfn "ERROR: Formula has the same value than with the original environment!"
            
            printfn "Would you like to add an accepting path to the invariant? (y/n)"
            answer := Console.ReadLine()
    else
        printfn "These conditions are sufficient to satisfy/break the invariant!"

    let f =
        if not (List.isEmpty (!allowed_paths))
        then
            let f = Formula.formula_from_marks env m' (!allowed_paths)
            Formula.simplify_value f
        else f

    printfn ""
    printfn "Invariant to add:"
    printfn "%s" (Printer.value_to_string decls f 0)
    
    ignore (Console.ReadLine())
    0

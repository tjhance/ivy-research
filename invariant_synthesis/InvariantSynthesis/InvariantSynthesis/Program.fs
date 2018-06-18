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
    let no_trace = Array.contains "-nt" argv

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
    printfn "Executing..."
    let (tr, env') =
        if no_trace then
            let (env',_) = Interpreter.execute_action md infos env name args
            (Trace.TrExprNotEvaluated (env,env',None), env')
        else
            let tr = TInterpreter.trace_action md infos env name (List.map (fun cv -> ExprConst cv) args)
            (tr, Trace.final_env_of_expr tr)
    if verbose
    then
        printfn "%A" tr

    let ((m,um,ad),formula,b) =
        if Trace.expr_is_fully_evaluated tr || no_trace
        then
            printfn "Please enter the index of the invariant to analyze:"

            List.iteri
                (
                    fun i v ->
                        match Interpreter.evaluate_value md infos env' v with
                        | ConstBool true -> Console.ForegroundColor <- ConsoleColor.Green
                        | ConstBool false -> Console.ForegroundColor <- ConsoleColor.Red
                        | _ -> Console.ResetColor()
                        printfn "%i. %s" i (Printer.value_to_string decls v 0)
                ) md.Invariants
            Console.ResetColor()

            let nb = Convert.ToInt32 (Console.ReadLine())
            let formula = List.item nb md.Invariants

            printfn "Generating marks for the formula (post execution)..."
            let (b,(m,um,ad)) = Synthesis.marks_for_value md infos env' Set.empty formula
            if verbose
            then
                printfn "%A" b
                printfn "%A" m
                printfn "%A" um
                printfn "%A" ad
            ((m,um,ad), Some formula, b)
        else
            printfn "Assertion failed... No invariant to analyze."
            printfn "Analyzing the reason of failure."
            (Synthesis.empty_config, None, ConstVoid)

    printfn "Going back through the action..."
    let (m,um,ad) =
        if no_trace then
            let (_,res) = Synthesis.marks_before_action md infos env name args (m,um,ad) false
            res
        else
            TSynthesis.marks_before_expression md infos tr (m,um,ad) false
    if verbose
    then
        printfn "%A" m
        printfn "%A" um
        printfn "%A" ad

    let (m', diff1) = Formula.simplify_marks infos md.Implications decls env m ad.d
    let (um', _) = Formula.simplify_marks infos md.Implications decls env um ad.d
    let f = Formula.formula_from_marks env (m', diff1) []
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
            let (tr_allowed, env_allowed') =
                if no_trace then
                    let (env',_) = Interpreter.execute_action md infos_allowed env_allowed name args
                    (Trace.TrExprNotEvaluated (env,env',None), env')
                else
                    let tr = TInterpreter.trace_action md infos_allowed env_allowed name (List.map (fun cv -> ExprConst cv) args)
                    (tr, Trace.final_env_of_expr tr)
            match formula with
            | None ->
                if Trace.expr_is_fully_evaluated tr_allowed
                then
                    let (m_al,_,ad_al) =
                        TSynthesis.marks_before_expression md infos_allowed tr_allowed Synthesis.empty_config false
                    if ad_al.md
                    then printfn "Warning: Some marks still are model-dependent! Generated invariant could be weaker than expected."
                    let (m_union, diff_union) = (Synthesis.marks_union m_al m', Set.union ad_al.d diff1)
                    let (m_al, diff_al) = Formula.simplify_marks infos md.Implications decls env_allowed m_union diff_union
                    let (m_al, diff_al) = (Synthesis.marks_diff m_al m', Set.difference diff_al diff1)
                    allowed_paths := (m_al,diff_al,env_allowed)::(!allowed_paths)
                else printfn "ERROR: Execution still fail!"
            | Some formula ->
                let (b_al,(m_al,um_al,ad_al)) =
                    Synthesis.marks_for_value md infos_allowed env_allowed' Set.empty formula
                if b_al <> b
                then
                    let (m_al,_,ad_al) =
                        if no_trace then
                            let (_,res) = Synthesis.marks_before_action md infos_allowed env_allowed name args (m_al,um_al,ad_al) false
                            res
                        else
                            TSynthesis.marks_before_expression md infos_allowed tr_allowed (m_al,um_al,ad_al) false
                    if ad_al.md
                    then printfn "ERROR: Some marks still are model-dependent!"
                    else
                        let (m_union, diff_union) = (Synthesis.marks_union m_al m', Set.union ad_al.d diff1)
                        let (m_al, diff_al) = Formula.simplify_marks infos md.Implications decls env_allowed m_union diff_union
                        let (m_al, diff_al) = (Synthesis.marks_diff m_al m', Set.difference diff_al diff1)
                        allowed_paths := (m_al,diff_al,env_allowed)::(!allowed_paths)
                else printfn "ERROR: Formula has the same value than with the original environment!"
            
            printfn "Would you like to add an accepting path to the invariant? (y/n)"
            answer := Console.ReadLine()
    else
        printfn "These conditions are sufficient to satisfy/break the invariant!"

    let f =
        if not (List.isEmpty (!allowed_paths))
        then
            let f = Formula.formula_from_marks env (m', diff1) (!allowed_paths)
            Formula.simplify_value f
        else f

    printfn ""
    printfn "Invariant to add:"
    printfn "%s" (Printer.value_to_string decls f 0)
    
    ignore (Console.ReadLine())
    0

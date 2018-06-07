open System.Text
open System
open AST

let read_until_line_jump () =
    let str = new StringBuilder()
    let line = ref "_"
    while !line <> "" do
        line := Console.ReadLine()
        ignore (str.Append(!line + Environment.NewLine))
    str.ToString()

[<EntryPoint>]
let main argv =

    let str = System.IO.File.ReadAllText("D:\\mini_test_parsed.sexpr");
    let test = ParserAST.deserialize_from_janestreet_sexpr str
    printfn "%A" test

    exit 0 ;

    let verbose = Array.contains "-v" argv
    let md = TestModule.Queue.queue_module
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
                    let a = Console.ReadLine()
                    match vd.Type with
                    | Void -> ConstVoid
                    | Bool -> ConstBool (Convert.ToBoolean a)
                    | Uninterpreted str -> ConstInt (str, Convert.ToInt32 a)
            )
            (find_action md name).Args
    printfn "Executing..."
    let tr = TInterpreter.trace_action md infos env name (List.map (fun cv -> ExprConst cv) args)
    printfn "Success !"
    if verbose
    then
        printfn "%A" tr

    let ((m,um,ad),formula,b) =
        if Trace.expr_is_fully_evaluated tr
        then
            printfn "Please enter the index of the invariant to analyze:"
            let nb = Convert.ToInt32 (Console.ReadLine())
            let formula = List.item nb md.Invariants

            printfn "Generating marks for the formula (post execution)..."
            let (b,(m,um,ad)) = Synthesis.marks_for_formula infos (Trace.final_env_of_expr tr) Set.empty formula
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
            (Synthesis.empty_config, None, false)

    printfn "Going back through the action..."
    let (m,um,ad) = TSynthesis.marks_before_expression md infos tr (m,um,ad) false
    if verbose
    then
        printfn "%A" m
        printfn "%A" um
        printfn "%A" ad

    let decls = Model.declarations_of_module md
    let (m', diff1) = Formula.simplify_marks infos md.Implications decls env m ad.d
    let (um', diff2) = Formula.simplify_marks infos md.Implications decls env um ad.d
    let f = Formula.formula_from_marks env (m', diff1) []
    let f = Formula.simplify_formula f
    printfn "%s" (Printer.formula_to_string decls f 0)
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
            let tr_allowed =
                TInterpreter.trace_action md infos_allowed env_allowed name (List.map (fun cv -> ExprConst cv) args)
            match formula with
            | None ->
                if Trace.expr_is_fully_evaluated tr_allowed <> b
                then
                    let (m_al,_,ad_al) =
                        TSynthesis.marks_before_expression md infos_allowed tr_allowed Synthesis.empty_config false
                    if ad_al.md
                    then printfn "ERROR: Some marks still are model-dependent!"
                    else
                        let (m_union, diff_union) = (Synthesis.marks_union m_al m', Set.union ad_al.d diff1)
                        let (m_al, diff_al) = Formula.simplify_marks infos md.Implications decls env m_union diff_union
                        let (m_al, diff_al) = (Synthesis.marks_diff m_al m', Set.difference diff_al diff1)
                        allowed_paths := (m_al,diff_al)::(!allowed_paths)
                else printfn "ERROR: Execution still fail!"
            | Some formula ->
                let (b_al,(m_al,um_al,ad_al)) =
                    Synthesis.marks_for_formula infos_allowed (Trace.final_env_of_expr tr_allowed) Set.empty formula
                if b_al <> b
                then
                    let (m_al,_,ad_al) =
                        TSynthesis.marks_before_expression md infos_allowed tr_allowed (m_al,um_al,ad_al) false
                    if ad_al.md
                    then printfn "ERROR: Some marks still are model-dependent!"
                    else
                        let (m_union, diff_union) = (Synthesis.marks_union m_al m', Set.union ad_al.d diff1)
                        let (m_al, diff_al) = Formula.simplify_marks infos md.Implications decls env m_union diff_union
                        let (m_al, diff_al) = (Synthesis.marks_diff m_al m', Set.difference diff_al diff1)
                        allowed_paths := (m_al,diff_al)::(!allowed_paths)
                else printfn "ERROR: Formula has the same value than with the original environment!"
            
            printfn "Would you like to add an accepting path to the invariant? (y/n)"
            answer := Console.ReadLine()
    else
        printfn "These conditions are sufficient to satisfy/break the invariant!"

    let f =
        if not (List.isEmpty (!allowed_paths))
        then
            let f = Formula.formula_from_marks env (m', diff1) (!allowed_paths)
            Formula.simplify_formula f
        else f

    printfn ""
    printfn "Invariant to add:"
    printfn "%s" (Printer.formula_to_string decls f 0)
    
    ignore (Console.ReadLine())
    0

(*
0:data ~= 1
0:data = q.first
1:data ~= q.first
0:incrementable.t ~= 1
0:incrementable.t ~= 2
0:incrementable.t = q.first_e
0:incrementable.t ~= q.next_e
1:incrementable.t ~= 2
1:incrementable.t ~= q.first_e
1:incrementable.t ~= q.next_e
2:incrementable.t ~= q.first_e
2:incrementable.t = q.next_e
q.content(1,1)
q.spec.content_f(0) = 0
q.spec.content_f(1) = 0
q.spec.content_f(2) = 0
0:incrementable.t < 1
0:incrementable.t < 2
1:incrementable.t < 2
incrementable.succ(0,1)

-----

0:data ~= 1
0:data = q.first
1:data ~= q.first
0:incrementable.t ~= 1
0:incrementable.t ~= 2
0:incrementable.t = q.first_e
0:incrementable.t ~= q.next_e
1:incrementable.t ~= 2
1:incrementable.t ~= q.first_e
1:incrementable.t ~= q.next_e
2:incrementable.t ~= q.first_e
2:incrementable.t = q.next_e
q.spec.content_f(0) = 0
q.spec.content_f(1) = 1
q.spec.content_f(2) = 0
0:incrementable.t < 1
0:incrementable.t < 2
1:incrementable.t < 2
incrementable.succ(0,1)
*)
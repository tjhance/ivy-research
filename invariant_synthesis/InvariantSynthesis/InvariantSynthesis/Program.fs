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
    let verbose = Array.contains "-v" argv
    let md = TestModule.Queue.queue_module
    printfn "Please enter constraints:"
    let str = read_until_line_jump ()
    printfn "Loading constraints..."
    let cs = ConstraintsParser.parse_from_str md str
    printfn "Building environment from constraints..."
    let (infos, env) = Model.constraints_to_env md cs
    printfn "Success !"
    if verbose
    then
        printfn "%A" infos
        printfn "%A" env

    printfn "Please enter the index of the invariant to analyze:"
    let nb = Convert.ToInt32 (Console.ReadLine())
    let formula = List.item nb md.Invariants
    printfn "Generating marks for the formula (pre execution)..."
    let (b,(m,um,ad)) = Synthesis.marks_for_formula infos env Set.empty formula
    printfn "Success !"
    if verbose
    then
        printfn "%A" b
        printfn "%A" m
        printfn "%A" um
        printfn "%A" ad

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
    let (env',ret) = Interpreter.execute_action md infos env name args
    printfn "Success !"
    if verbose
    then
        printfn "%A" ret
        printfn "%A" env'

    printfn "Press enter to proceed to computation."
    ignore (Console.ReadLine())

    printfn "Generating marks for the formula (post execution)..."
    let (b,(m,um,ad)) = Synthesis.marks_for_formula infos env' Set.empty formula
    printfn "Success !"
    if verbose
    then
        printfn "%A" b
        printfn "%A" m
        printfn "%A" um
        printfn "%A" ad

    printfn "Press enter to resume computation."
    ignore (Console.ReadLine())

    printfn "Going back through the action..."
    let (_,(m,um,ad)) = Synthesis.marks_before_action md infos env name args (m,um,ad) false
    printfn "Success !"
    if verbose
    then
        printfn "%A" b
        printfn "%A" m
        printfn "%A" um
        printfn "%A" ad

    printfn "Press enter to compute formula."
    ignore (Console.ReadLine())

    let decls = Model.declarations_of_module md
    let (m', ad1) = Formula.simplify_marks infos md.Implications decls env m ad
    let (um', ad2) = Formula.simplify_marks infos md.Implications decls env um ad
    let f = Formula.formula_from_marks env m' ad1
    let f = Formula.simplify_formula f
    printfn "%s" (Printer.formula_to_string decls f 0)
    printfn ""

    if ad.md
    then
        printfn "These conditions may not be sufficient to satisfy/break the invariant!"
        printfn "Would you like to add an accepting path to the invariant? (y/n)"
        let answer = ref (Console.ReadLine())
        while !answer = "y" do
            printfn "Please modify some constraints on the environment to fix the initial environment."
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
            let env_allowed = Model.constraints_to_env md (cs@cs')
            printfn "ERROR: Not implemented"

            printfn "Would you like to add an accepting path to the invariant? (y/n)"
            answer := Console.ReadLine()
    else
        printfn "These conditions are sufficient to satisfy/break the invariant!"

    printfn ""
    printfn "Invariant to add:"
    let f = Formula.simplify_formula (Not f)
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
~q.empty
q.spec.content_f(0) = 0
q.spec.content_f(1) = 1
q.spec.content_f(2) = 0
0:incrementable.t < 1
0:incrementable.t < 2
1:incrementable.t < 2
incrementable.succ(0,1)
*)
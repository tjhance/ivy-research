open System.Text
open System

let read_until_line_jump () =
    let str = new StringBuilder()
    let line = ref "_"
    while !line <> "" do
        line := Console.ReadLine()
        ignore (str.Append(!line))
    str.ToString()

[<EntryPoint>]
let main argv =
    let m = TestModule.Queue.queue_module
    printfn "Please enter constraints:"
    let str = read_until_line_jump ()
    printfn "Loading constraints..."
    let cs = ConstraintsParser.parse_from_str m str
    printfn "Building environment from constraints..."
    let (infos, env) = Model.constraints_to_env m cs
    printfn "Success !"
    ignore (Console.ReadLine())
    0

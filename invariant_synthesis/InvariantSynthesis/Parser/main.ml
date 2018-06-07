open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error action lexbuf =
  try
    match action with
    | "all" ->
      let res = (Parser.all_elements (Lexer.read false) lexbuf) in
      if res = [] then None
      else Some (AST.sexp_of_parsed_elements res)
    | "expr" -> Some (AST.sexp_of_parsed_expression (Parser.next_expression (Lexer.read false) lexbuf))
    | "stat" -> Some (AST.sexp_of_parsed_statement (Parser.next_statement (Lexer.read false) lexbuf))
    | "elem" -> Some (AST.sexp_of_parsed_element (Parser.next_element (Lexer.read false) lexbuf))
    | _ -> Some (AST.sexp_of_parsed_expression (Parser.next_expression (Lexer.read false) lexbuf))
  with
  | Lexer.SyntaxError msg ->
    Printf.fprintf stderr "[Lexing] %a: %s\n%!" print_position lexbuf msg;
    None
  | Parser.Error ->
    Printf.fprintf stderr "[Parsing] %a: syntax error\n%!" print_position lexbuf;
    None

let rec parse_and_print action out_chan lexbuf =
  match parse_with_error action lexbuf with
  | None -> ()
  | Some sexp ->
    Printf.fprintf out_chan "%s\n%!" (Sexplib.Sexp.to_string sexp) ;
    parse_and_print action out_chan lexbuf

let () =
  let action =
      if Array.length Sys.argv > 1
      then Sys.argv.(1)
      else ""
    in
  let (chan, filename) =
    if Array.length Sys.argv > 2
    then
      let filename = Sys.argv.(2) in
      (open_in filename, filename)
    else
      (stdin, "stdin")
    in
  let out_chan =
    if Array.length Sys.argv > 3
    then
      open_out Sys.argv.(3)
    else
      stdout
    in
  let lexbuf = Lexing.from_channel chan in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_and_print action out_chan lexbuf;
  close_out out_chan ; close_in chan

module Printer

    open AST

    let const_value_to_string cv =
        match cv with
        | ConstVoid -> "()"
        | ConstBool b -> sprintf "%b" b
        | ConstInt (_,i) -> sprintf "%i" i
        | ConstEnumerated (_,str) -> sprintf "%s" str

    let type_to_string t =
        match t with
        | Void -> "void"
        | Bool -> "bool"
        | Uninterpreted str -> str
        | Enumerated str -> str

    let var_decl_to_string (vd:VarDecl) =
        match vd.Representation.DisplayName with
        | None -> sprintf "%s:%s" vd.Name (type_to_string vd.Type)
        | Some s -> sprintf "%s:%s" s (type_to_string vd.Type)

    let list_to_args_str lst =
        match lst with
        | [] -> ""
        | h::lst -> sprintf "(%s)" (List.fold (sprintf "%s, %s") h lst)

    let add_parenthesis_if_needed str prec env_prec =
        if prec < env_prec
        then sprintf "(%s)" str
        else str

    let rec value_to_string (decls:Model.Declarations) v prec =
        let fun_macro_to_string str vs rep =
            let str = 
                match rep.DisplayName with
                | None -> str
                | Some str -> str
            if Set.contains Infix rep.Flags
            then
                (*let str = *)
                sprintf "(%s %s %s)" ((fun v -> value_to_string decls v 6) (List.head vs)) str ((fun v -> value_to_string decls v 6) (List.head (List.tail vs)))
                //add_parenthesis_if_needed str 6 prec
            else sprintf "%s%s" str (list_to_args_str (List.map (fun v -> value_to_string decls v 0) vs))
        match v with
        // ----- Syntaxic sugars -----
        | ValueNot (ValueEqual (v1,v2)) ->
            let str = sprintf "%s ~= %s" (value_to_string decls v1 5) (value_to_string decls v2 5)
            add_parenthesis_if_needed str 5 prec
        | ValueEqual (v, ValueConst (ConstBool true))
        | ValueEqual (ValueConst (ConstBool true), v) ->
            sprintf "%s" (value_to_string decls v prec)
        | ValueEqual (v, ValueConst (ConstBool false))
        | ValueEqual (ValueConst (ConstBool false), v) ->
            let str = sprintf "~%s" (value_to_string decls v 7)
            add_parenthesis_if_needed str 7 prec
        // ---------------------------
        | ValueConst cv -> const_value_to_string cv
        | ValueStar _ -> "*"
        | ValueVar str ->
                try
                    match (Map.find str decls.v).Representation.DisplayName with
                    | None -> str
                    | Some str -> str
                with :? System.Collections.Generic.KeyNotFoundException -> str
        | ValueFun (str, vs) ->
            try
                let d = Map.find str decls.f
                fun_macro_to_string str vs d.Representation
            with :? System.Collections.Generic.KeyNotFoundException ->
                sprintf "%s%s" str (list_to_args_str (List.map (fun v -> value_to_string decls v 0) vs))
        | ValueMacro (str, vs) ->
            try
                let d = Map.find str decls.m
                fun_macro_to_string str vs d.Representation
            with :? System.Collections.Generic.KeyNotFoundException ->
                sprintf "%s%s" str (list_to_args_str (List.map (fun v -> value_to_string decls v 0) vs))
        | ValueInterpreted (str, vs) ->
            try
                let d = Map.find str decls.i
                fun_macro_to_string str vs d.Representation
            with :? System.Collections.Generic.KeyNotFoundException ->
                sprintf "%s%s" str (list_to_args_str (List.map (fun v -> value_to_string decls v 0) vs))
        | ValueEqual (v1, v2) ->
            let str = sprintf "%s = %s" (value_to_string decls v1 5) (value_to_string decls v2 5)
            add_parenthesis_if_needed str 5 prec
        | ValueOr (f1,f2) ->
            let str = sprintf "%s | %s" (value_to_string decls f1 3) (value_to_string decls f2 3)
            add_parenthesis_if_needed str 3 prec
        | ValueAnd (f1,f2) ->
            let str = sprintf "%s & %s" (value_to_string decls f1 4) (value_to_string decls f2 4)
            add_parenthesis_if_needed str 4 prec
        | ValueNot f ->
            let str = sprintf "~%s" (value_to_string decls f 7)
            add_parenthesis_if_needed str 7 prec
        | ValueForall (vd, f) ->
            let decls = Model.add_var_declaration vd decls
            let str = sprintf "∀ %s. %s" (var_decl_to_string vd) (value_to_string decls f 1)
            add_parenthesis_if_needed str 1 prec
        | ValueExists (vd, f) ->
            let decls = Model.add_var_declaration vd decls
            let str = sprintf "∃ %s. %s" (var_decl_to_string vd) (value_to_string decls f 1)
            add_parenthesis_if_needed str 1 prec
        | ValueImply (f1,f2) ->
            let str = sprintf "%s -> %s" (value_to_string decls f1 2) (value_to_string decls f2 2)
            add_parenthesis_if_needed str 2 prec
        | ValueSomeElse (d,f,v) ->
            let decls' = Model.add_var_declaration d decls
            sprintf "(some %s. %s else %s)" (var_decl_to_string d) (value_to_string decls' f 0) (value_to_string decls v 0)
        | ValueIfElse (f,v1,v2) ->
            sprintf "(%s if %s else %s)" (value_to_string decls v1 0) (value_to_string decls f 0) (value_to_string decls v2 0)

    (*
    Precedence:
    ~ : 7
    infix : 6 (parenthesis forced)
    = ~= : 5
    & : 4
    | : 3
    -> : 2
    F E : 1
    *)

    let mvalue_to_string (decls:Model.Declarations) (v: MinimalAST.Value) : string =
        value_to_string decls (MinimalAST.value2ast v) 0

    let z3value_to_string (decls:Model.Declarations) (v: WPR.Z3Value) : string =
      let rec get_conjuncts (v: WPR.Z3Value) =
          match v with
              | WPR.Z3And (a, b) -> List.append (get_conjuncts a) (get_conjuncts b)
              | _ -> [v]

      let rec get_disjuncts (v: WPR.Z3Value) =
          match v with
              | WPR.Z3Or (a, b) -> List.append (get_disjuncts a) (get_disjuncts b)
              | _ -> [v]

      let name_map : Map<string, string> ref = ref Map.empty
      let i = ref 0
      let new_name () =
        let j = !i
        i := j + 1
        string (char (int 'A' + int (j % 26))) + (if j < 26 then "" else (string (j / 26)))
      let get_name (x:string) =
        if Map.containsKey x !name_map then
          Map.find x !name_map
        else
          let n = new_name()
          name_map := Map.add x n !name_map
          n

      let rec aux v =
          let forall_exists symbol (vdecl: AST.VarDecl) v =
            let name = match vdecl.Representation.DisplayName with | None -> vdecl.Name | Some s -> s
            let u = symbol + " " + get_name name + ":" + type_to_string vdecl.Type + " . " + aux v
            "(" + u + ")"

          match v with
            | WPR.Z3Const c -> value_to_string decls (AST.ValueConst c) 0
            | WPR.Z3Var s -> get_name s
            | WPR.Z3Fun (s, vs) -> s + "(" + (String.concat ", " (List.map aux vs)) + ")"
            | WPR.Z3Equal (a, b) -> aux a + " = " + aux b
            | WPR.Z3Or _ -> "(" + (String.concat " | " (List.map aux (get_disjuncts v))) + ")"
            | WPR.Z3Imply (a, b) -> "(" + aux a + " -> " + aux b + ")"
            | WPR.Z3And (a, b) -> "(" + (String.concat " & " (List.map aux (get_conjuncts v))) + ")"
            | WPR.Z3Not (WPR.Z3Equal (a, b)) -> aux a + " ~= " + aux b
            | WPR.Z3Not a -> "~" + aux a
            | WPR.Z3IfElse (a,b,c) -> "(if " + aux a + " then " + aux b + " else " + aux c + ")"
            | WPR.Z3Forall (de, b) -> forall_exists "∀" de b
            | WPR.Z3Exists (de, b) -> forall_exists "∃" de b
            | WPR.Z3Hole -> "_"

      aux v

    let varmark_to_string decls (env:Model.Environment) str =
        let value = Map.find str env.v
        let v = ValueEqual (ValueVar str, ValueConst value)
        value_to_string decls v 0

    let funmark_to_string decls (env:Model.Environment) (str, cvs) =
        let value = Map.find (str, cvs) env.f
        let cvs = List.map (fun cv -> ValueConst cv) cvs
        let v = ValueEqual (ValueFun (str, cvs), ValueConst value)
        value_to_string decls v 0


    let print_model infos (env: Model.Environment) =
        let to_str v = match v with
                            | ConstInt (_,v) -> v.ToString()
                            | _ -> failwith "print_model expected ConstInt"

        printfn "%A\n" infos
        Map.iter (fun (name, l) -> fun value ->
          match value with
          | ConstBool v ->
            if v then
              printfn "%s(%s)" name (String.concat ", " (List.map to_str l))
          | ConstInt (_,i) ->
            printfn "%s(%s) = %d" name (String.concat ", " (List.map to_str l)) i
          | _ -> failwith "print_model expected bool or int"
        ) env.f
        printfn "%A\n" env.v

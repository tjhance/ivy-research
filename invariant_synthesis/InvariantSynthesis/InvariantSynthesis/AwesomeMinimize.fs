// Let's hope this file is named accurately
module AwesomeMinimize
  open WPR
  open MinimalAST

  let push_negations_down (v: Z3Value) =
      let rec aux f neg = match f with
                            | Z3Const _
                            | Z3Var _
                            | Z3Fun _
                            | Z3Equal _
                            | Z3IfElse _ ->
                                if neg then
                                  Z3Not f
                                else
                                  f
                            | Z3Or (a, b) ->
                                if neg then
                                  Z3And (aux a neg, aux b neg)
                                else
                                  Z3Or (aux a neg, aux b neg)
                            | Z3And (a, b) ->
                                if neg then
                                  Z3Or (aux a neg, aux b neg)
                                else
                                  Z3And (aux a neg, aux b neg)
                            | Z3Imply (a, b) -> aux (Z3Or (Z3Not a, b)) neg
                            | Z3Not a -> aux a (not neg)
                            | Z3Forall (de, b) ->
                                if neg then
                                  Z3Exists (de, aux b neg)
                                else
                                  Z3Forall (de, aux b neg)
                            | Z3Exists (de, b) ->
                                if neg then
                                  Z3Forall (de, aux b neg)
                                else
                                  Z3Exists (de, aux b neg)
                            | Z3Hole -> failwith "fail: push_negations_down Z3Hole"
      aux v false


  let rec get_conjuncts (v: Z3Value) =
      match v with
          | Z3And (a, b) -> List.append (get_conjuncts a) (get_conjuncts b)
          | Z3Forall (de, b) -> List.map (fun x -> Z3Forall (de, x)) (get_conjuncts b)
          | _ -> [v]

  let rec get_disjuncts (v: Z3Value) =
      match v with
          | Z3Or (a, b) -> List.append (get_conjuncts a) (get_conjuncts b)
          | _ -> [v]

  let rec and_list (v: Z3Value list) : Z3Value =
      match v with
          | [] -> Z3Const (AST.ConstBool true)
          | [x] -> x
          | x :: rest -> Z3And (x, and_list rest)

  let rec or_list (v: Z3Value list) : Z3Value =
      match v with
          | [] -> Z3Const (AST.ConstBool false)
          | [x] -> x
          | x :: rest -> Z3Or (x, or_list rest)

  type MValue =
      | MConst of ConstValue
      | MVar of string
      | MFun of string * List<MValue>
      | MEqual of MValue * MValue
      | MOr of (MValue list) ref
      | MAnd of MValue * MValue
      | MNot of MValue
      | MIfElse of MValue * MValue * MValue
      | MForall of VarDecl * MValue
      | MExists of VarDecl * MValue

  let z3_to_m v =
      let rec aux v =
          match v with
              | Z3Const c -> MConst c
              | Z3Var s -> MVar s
              | Z3Fun (s, vs) -> MFun (s, List.map aux vs)
              | Z3Equal (a, b) -> MEqual (aux a, aux b)
              | Z3Or _ -> MOr (ref (List.map aux (get_disjuncts v)))
              | Z3Imply _ -> failwith "z3_to_m: Z3Imply not expected"
              | Z3And (a, b) -> MAnd (aux a, aux b)
              | Z3Not a -> MNot (aux a)
              | Z3IfElse (a,b,c) -> MIfElse (aux a, aux b, aux c)
              | Z3Forall (de, b) -> MForall (de, aux b)
              | Z3Exists (de, b) -> MExists (de, aux b)
              | Z3Hole -> failwith "z3_to_m: hole not expected"
      aux v

  let m_to_z3 v =
      let rec aux v =
          match v with
              | MConst c -> Z3Const c
              | MVar s -> Z3Var s
              | MFun (s, vs) -> Z3Fun (s, List.map aux vs)
              | MEqual (a, b) -> Z3Equal (aux a, aux b)
              | MOr l -> or_list (List.map aux !l)
              | MAnd (a, b) -> Z3And (aux a, aux b)
              | MNot a -> Z3Not (aux a)
              | MIfElse (a,b,c) -> Z3IfElse (aux a, aux b, aux c)
              | MForall (de, b) -> Z3Forall (de, aux b)
              | MExists (de, b) -> Z3Exists (de, aux b)
      aux v

  let minimize (md:AST.ModuleDecl<'a,'b>) (mmd:MinimalAST.ModuleDecl<'a,'b>) (decls:Model.Declarations) actions init_actions (v: Z3Value) : Z3Value =
    let v = simplify_z3_value v
    let v = push_negations_down v

    let axioms = Solver.z3_formula_for_axioms mmd
    let k = 2
    let is_valid (v: Z3Value) : bool =
      let f = Z3And (axioms, Solver.has_k_exec_counterexample_formula v actions init_actions k)
      printfn ""
      printfn "formula: %s" (Printer.z3value_to_string decls v)
      //printfn "formula: %s" (Printer.z3value_to_string decls f)
      match Solver.check_z3_formula md [] f 5000 with
        | Solver.SolverResult.UNKNOWN -> failwith "got UNKNOWN"
        | Solver.SolverResult.UNSAT -> printfn "unsat\n"; true
        | Solver.SolverResult.SAT _ -> printfn "sat\n"; false

    let minimize_part v =
      printfn "trying to minimize %s" (Printer.z3value_to_string decls v)
      let tree = z3_to_m v

      let rec traverse_and_edit_tree subtree : unit =
        match subtree with
          | MForall (de, a) ->
              traverse_and_edit_tree a
          | MExists (de, a) ->
              traverse_and_edit_tree a
          | MAnd (a, b) ->
              traverse_and_edit_tree a
              traverse_and_edit_tree b
          | MOr lref ->
              let pieces = ref (!lref)
              let chosen = ref []
              while (!pieces) <> [] do
                match !pieces with
                  | [] -> failwith "expected one element"
                  | (piece :: rest) ->
                      pieces := rest
                      lref := List.append (!chosen) (!pieces)
                      let can_drop_piece = is_valid (m_to_z3 tree)
                      if not can_drop_piece then
                        chosen := List.append (!chosen) [piece]
              lref := !chosen

              List.iter traverse_and_edit_tree (!lref)
          | _ ->
              ()

      traverse_and_edit_tree tree
      let result = m_to_z3 tree
      printfn "trying to minimize %s" (Printer.z3value_to_string decls result)
      result

    let minimized = and_list (List.map minimize_part (get_conjuncts v))
    minimized

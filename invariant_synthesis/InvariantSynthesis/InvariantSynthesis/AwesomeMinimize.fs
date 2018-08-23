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
          | _ -> [v]

  let rec get_disjuncts (v: Z3Value) =
      match v with
          | Z3Or (a, b) -> List.append (get_conjuncts a) (get_conjuncts b)
          | _ -> [v]

  let rec and_list (v: Z3Value list) : Z3Value=
      match v with
          | [] -> Z3Const (AST.ConstBool true)
          | [x] -> x
          | x :: rest -> Z3And (x, and_list rest)

  let rec or_list (v: Z3Value list) : Z3Value =
      match v with
          | [] -> Z3Const (AST.ConstBool false)
          | [x] -> x
          | x :: rest -> Z3Or (x, or_list rest)

  let minimize (v: Z3Value) : Z3Value =
    let v = simplify_z3_value v
    let v = push_negations_down v

    let is_valid (v: Z3Value) : bool =
      failwith "is_valid not impl"

    let minimize_part v =
      let pieces = ref (get_disjuncts v)
      let chosen = ref []
      while (!pieces) <> [] do
        match !pieces with
          | [] -> failwith "expected one element"
          | (piece :: rest) ->
              pieces := rest
              if not (is_valid (or_list (List.append (!chosen) rest))) then
                chosen := List.append (!chosen) [piece]
      or_list (!chosen)

    let minimized = and_list (List.map minimize_part (get_conjuncts v))
    minimized

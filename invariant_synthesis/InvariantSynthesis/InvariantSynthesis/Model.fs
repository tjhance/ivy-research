module Model

    (* TYPES TO DESCRIBE (FINITE) MODELS AND ENVIRONMENTS *)
    open AST

    type BoundConstraint = string * int // For custom types, the number of elements - 1
    type FunConstraint = string * List<ConstValue> * ConstValue
    type VarConstraint = string * ConstValue

    type Constraint =
        | Bound of BoundConstraint
        | Function of FunConstraint
        | Variable of VarConstraint

    type Model = { b : List<BoundConstraint> ; f : List<FunConstraint>; v : List<VarConstraint> }
    type Model' = List<Constraint>


    type TypeInfos = Map<string, int> // For now: only contains bounds for each type

    type FunEnv = Map<string * List<ConstValue>, ConstValue>
    type VarEnv = Map<string, ConstValue>

    type Environment = { f : FunEnv; v : VarEnv }

    type VarDecls = Map<string, VarDecl>
    type FunDecls = Map<string, FunDecl>

    type Declarations = { f : FunDecls; v : VarDecls }

    let declarations_of_module (md:ModuleDecl) =
        let aux acc (d:VarDecl) =
            Map.add d.Name d acc
        let vars = List.fold aux Map.empty md.Vars
        let aux acc (d:FunDecl) =
            Map.add d.Name d acc
        let funs = List.fold aux Map.empty md.Funs
        { f = funs; v = vars }

    let add_var_declaration (d:VarDecl) (ds:Declarations) =
        { ds with v=Map.add d.Name d ds.v }

    let type_default_value t =
        match t with
        | Void -> ConstVoid
        | Bool -> ConstBool false
        | Uninterpreted str -> ConstInt (str, 0)

    let all_values infos data_type =
        match data_type with
        | Void -> Seq.singleton ConstVoid
        | Bool -> [ConstBool false; ConstBool true] |> Seq.ofList
        | Uninterpreted s ->
            let max = Map.find s infos
            seq { for x in 0..max -> ConstInt (s, x) }

    let pick_value infos data_type =
        Seq.head (all_values infos data_type)

    let rec all_values_ext infos lst =
        match lst with
        | [] -> Seq.singleton []
        | t::lst ->
            let res = all_values_ext infos lst
            let pos = all_values infos t
            let res = Seq.map (fun lst -> Seq.map (fun v -> v::lst) pos) res
            Seq.concat res

    // Note: If some constraints are contradictory, the last one has the last word
    let constraints_to_env (m:ModuleDecl) cs : (TypeInfos * Environment) =
        // Type infos
        // Init
        let type_infos = List.fold (fun acc (tdecl:TypeDecl) -> Map.add tdecl.Name 0 acc) Map.empty m.Types
        // Apply constraints
        let type_infos =
            List.fold
                (fun acc c ->
                    match c with
                    | Function _ | Variable _ -> acc
                    | Bound (str, i) ->
                        let old_i = Map.find str type_infos
                        Map.add str (max i old_i) acc
                ) type_infos cs

        // Environment
        // Init
        let var_env =
            List.fold
                (fun acc (vdecl:VarDecl) -> Map.add vdecl.Name (type_default_value vdecl.Type) acc)
                Map.empty m.Vars
        let fun_env =
            List.fold
                (fun acc (fdecl:FunDecl) ->
                    Seq.fold (fun acc input ->
                        Map.add (fdecl.Name, input) (type_default_value fdecl.Output) acc)
                        acc (all_values_ext type_infos fdecl.Input)
                ) Map.empty m.Funs
        // Apply constraints
        let (var_env, fun_env) =
            List.fold
                (fun (v,f) c ->
                    match c with
                    | Function (str, input, output) -> (v, Map.add (str, input) output f)
                    | Variable (str, output) -> (Map.add str output v, f)
                    | Bound _ -> (v,f)
                ) (var_env, fun_env) cs

        (type_infos, { f = fun_env ; v = var_env })

module TwoState
    open WPR
    open MinimalAST

    type FunType = List<Type> * Type

    type Context = {
      cx_var_map: Map<string, string * Type>;
      cx_fun_map: Map<string, string * FunType>;
    }

    type TwoState = {
      pre: Context;
      post: Context;

      formula: Z3Value;

      vars: Map<string, Type>
      funs: Map<string, FunType>
    }

    let empty_context : Context = { cx_var_map = Map.empty ; cx_fun_map = Map.empty }

    let cx_lookup_var (s: string) (cx: Context) : string =
      if not (Map.containsKey s cx.cx_var_map) then
        failwith ("could not look up var: " + s)
      fst (Map.find s cx.cx_var_map)

    let cx_lookup_var_type (s: string) (cx: Context) : Type =
      if not (Map.containsKey s cx.cx_var_map) then
        failwith ("could not look up var: " + s)
      snd (Map.find s cx.cx_var_map)

    let cx_lookup_fun (s: string) (cx: Context) : string =
      if not (Map.containsKey s cx.cx_fun_map) then
        failwith ("could not look up fun: " + s)
      fst (Map.find s cx.cx_fun_map)

    let cx_lookup_fun_type (s: string) (cx: Context) : FunType =
      if not (Map.containsKey s cx.cx_fun_map) then
        failwith ("could not look up fun: " + s)
      snd (Map.find s cx.cx_fun_map)

    let cx_add_var (s: string) (t: string) (ty: Type) (cx: Context) : Context =
      (*
      printfn "adding key %s" s
      if Map.containsKey s cx.cx_var_map then
        failwith ("cx_add_var: expected var " + s + " not to be in map")
        *)
      {cx_var_map = Map.add s (t, ty) cx.cx_var_map ; cx_fun_map = cx.cx_fun_map }

    let cx_update_var (s: string) (t: string) (ty: Type) (cx: Context) : Context =
      if not (Map.containsKey s cx.cx_var_map) then
        failwith "cx_update_var: expected var to be in map"
      if snd (Map.find s cx.cx_var_map) <> ty then
        failwith "cx_update_var: expected ty to match"
      {cx_var_map = Map.add s (t, ty) cx.cx_var_map ; cx_fun_map = cx.cx_fun_map }

    let cx_add_fun (s: string) (t: string) (ty: FunType) (cx: Context) : Context =
      if Map.containsKey s cx.cx_fun_map then
        failwith "cx_add_fun: expected fun not to be in map"
      {cx_fun_map = Map.add s (t, ty) cx.cx_fun_map ; cx_var_map = cx.cx_var_map }

    let cx_update_fun (s: string) (t: string) (ty: FunType) (cx: Context) : Context =
      if not (Map.containsKey s cx.cx_fun_map) then
        failwith "cx_update_fun: expected fun to be in map"
      if snd (Map.find s cx.cx_fun_map) <> ty then
        failwith "cx_update_fun: expected ty to match"
      {cx_fun_map = Map.add s (t, ty) cx.cx_fun_map ; cx_var_map = cx.cx_var_map }

    let lit_true = Z3Const (AST.ConstBool true)

    let mergeMaps maps = Map.ofList (List.concat (List.map Map.toList maps))

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


    let name_id = ref 0
    let new_name (basename: string) =
      let id = !name_id
      name_id := !name_id + 1
      "__" + basename + "_" + id.ToString()

    let funs_are_equal_expr (fn1 : string) (fn2 : string) (ty: FunType) =
      let (arg_types, _) = ty
      let vars =
        List.map (fun ty ->
          let name = new_name "x"
          let decl = AST.default_var_decl name ty
          name, decl
        ) arg_types
      let inner =
        Z3Equal (
          Z3Fun (fn1, List.map (fun (v, _) -> Z3Var v) vars),
          Z3Fun (fn2, List.map (fun (v, _) -> Z3Var v) vars)
        )
      List.fold (fun expr -> fun (_, decl) -> Z3Forall (decl, expr)) inner vars

    let make_two_state_for_stmt (mmd : ModuleDecl<'a,'b>) (args: List<VarDecl>) (content: Statement) =
      let skolem_vars : Map<string, Type> ref = ref Map.empty
      let skolem_funs : Map<string, FunType> ref = ref Map.empty

      let new_skolem_var (basename : string) (ty : Type) : string =
        let name = new_name basename
        skolem_vars := Map.add name ty !skolem_vars
        name

      let new_skolem_fun (basename : string) (ty : FunType) : string =
        let name = new_name basename
        skolem_funs := Map.add name ty !skolem_funs
        name

      let new_var (basename : string) (ty: Type) : string * VarDecl =
        let name = new_name basename
        (name, AST.default_var_decl name ty)

      let expression (cx : Context) (v : Value) : Z3Value * Z3Value =
        let rec aux cx v : Z3Value * Z3Value =
          match v with
            | ValueConst c -> (lit_true, Z3Const c)
            | ValueStar ty -> (lit_true, Z3Var (new_skolem_var "star" ty))
            | ValueVar v -> (lit_true, Z3Var (cx_lookup_var v cx))
            | ValueFun (fname, args) ->
                let ar = List.map (aux cx) args
                let ass = and_list (List.map fst ar)
                let res = Z3Fun (cx_lookup_fun fname cx, List.map snd ar)
                (ass, res)
            | ValueEqual (a, b) ->
                let (ass1, res1) = aux cx a
                let (ass2, res2) = aux cx b
                (Z3And (ass1, ass2), Z3Equal (res1, res2))
            | ValueOr (a, b) ->
                let (ass1, res1) = aux cx a
                let (ass2, res2) = aux cx b
                (Z3And (ass1, ass2), Z3Or (res1, res2))
            | ValueAnd (a, b) ->
                let (ass1, res1) = aux cx a
                let (ass2, res2) = aux cx b
                (Z3And (ass1, ass2), Z3And (res1, res2))
            | ValueNot a ->
                let (ass1, res1) = aux cx a
                (ass1, Z3Not res1)
            | ValueSomeElse (decl, cond, default_v) ->
                let v = new_skolem_var decl.Name decl.Type
                let (qv, qvdecl) = new_var decl.Name decl.Type
                let (ass0, z3_default_v) = aux cx default_v
                let (ass1, res_cond) = aux (cx_add_var decl.Name v decl.Type cx) cond
                let (ass2, res_cond') = aux (cx_add_var decl.Name qv decl.Type cx) cond
                let ass = (
                  Z3Or (
                    res_cond,
                    Z3And (
                      Z3Equal (Z3Var v, z3_default_v),
                      Z3Forall (qvdecl, Z3Not res_cond')
                    )
                  )
                )
                (and_list [ass0; ass1; ass2; ass], Z3Var v)
            | ValueIfElse (a, b, c) ->
                let (ass1, res1) = aux cx a
                let (ass2, res2) = aux cx b
                let (ass3, res3) = aux cx c
                (and_list [ass1; ass2; ass3], Z3IfElse (res1, res2, res3))
            | ValueForall (de, v) ->
                let (ass1, res1) = aux (cx_add_var de.Name de.Name de.Type cx) v
                (ass1, Z3Forall (de, res1))
            | ValueExists (de, v) ->
                let (ass1, res1) = aux (cx_add_var de.Name de.Name de.Type cx) v
                (ass1, Z3Exists (de, res1))
            | ValueInterpreted _ -> failwith "TODO implement ValueInterpeted"
        aux cx v

      let merge (cond_var: string) (cx_orig: Context) (cx_then: Context) (cx_else: Context) =
        let assms = ref []
        let cx_var_map =
          Map.map (fun var_name -> fun _ ->
            let var_then = cx_lookup_var var_name cx_then
            let var_else = cx_lookup_var var_name cx_else
            let ty = cx_lookup_var_type var_name cx_then
            let ty2 = cx_lookup_var_type var_name cx_else
            if ty <> ty2 then
              failwith "expected types the same"
            if var_then = var_else then
              var_then, ty
            else
              let v = new_skolem_var var_name ty
              assms := (Z3Equal (Z3Var v, Z3IfElse (Z3Var cond_var, Z3Var var_then, Z3Var var_else))) :: !assms
              v, ty
          ) cx_orig.cx_var_map

        let cx_fun_map =
          Map.map (fun fun_name -> fun _ ->
            let fun_then = cx_lookup_fun fun_name cx_then
            let fun_else = cx_lookup_fun fun_name cx_else
            let ty = cx_lookup_fun_type fun_name cx_then
            let ty2 = cx_lookup_fun_type fun_name cx_else
            if ty <> ty2 then
              failwith "expected types the same"
            if fun_then = fun_else then
              fun_then, ty
            else
              let f = new_skolem_fun fun_name ty
              let arg_types = fst ty
              let new_vars =
                List.map (fun arg_ty ->
                  new_var "x" arg_ty
                ) arg_types
              let inner_assumption =
                (Z3Equal (
                  Z3Fun (f, List.map (fun (v, _) -> Z3Var v) new_vars),
                  Z3IfElse (Z3Var cond_var,
                      Z3Fun (fun_then, (List.map (fun (v, _) -> Z3Var v) new_vars)),
                      Z3Fun (fun_else, (List.map (fun (v, _) -> Z3Var v) new_vars))
                  )
                ))
              let full_assumption =
                List.fold (fun assm -> fun (_, vdecl) ->
                  Z3Forall (vdecl, assm)
                ) inner_assumption new_vars
              assms := full_assumption :: !assms
              f, ty
          ) cx_orig.cx_fun_map

        (and_list !assms, { cx_var_map = cx_var_map ; cx_fun_map = cx_fun_map })

      let rec statement (cx: Context) (stmt: Statement) : Z3Value * Context =
        match stmt with
          | AtomicGroup stmts ->
            List.fold (fun (ass0, cx) -> fun stmt ->
              let ass1, cx' = statement cx stmt
              (Z3And (ass0, ass1), cx')
            ) (lit_true, cx) stmts
          | NewBlock (var_decls, stmts) ->
            let cx =
              List.fold (fun cx -> fun (var_decl : VarDecl) ->
                let v = new_skolem_var var_decl.Name var_decl.Type
                cx_add_var var_decl.Name v var_decl.Type cx
              ) cx var_decls
            List.fold (fun (ass0, cx) -> fun stmt ->
              let ass1, cx' = statement cx stmt
              (Z3And (ass0, ass1), cx')
            ) (lit_true, cx) stmts
            (* TODO remove the vars that were added from cx *)
          | VarAssign (varname, value) ->
            let ass0, z3value = expression cx value
            let ty = cx_lookup_var_type varname cx
            let ass, value_var =
              match z3value with
                | Z3Var name -> ass0, name
                | _ ->
                  let v = new_skolem_var "x" ty
                  Z3And (ass0, (Z3Equal (Z3Var v, z3value))), v
            (ass, cx_update_var varname value_var ty cx)
          | VarAssignAction _ -> failwith "TwoState: TODO implement VarAssignAction"
          | FunAssign (funname, args, value) ->
            let fun_ty = cx_lookup_fun_type funname cx
            let cx_ = ref cx
            let new_vars =
              List.map (fun (arg : VarDecl) ->
                let ty = arg.Type
                let v, vdecl = new_var arg.Name ty
                cx_ := cx_add_var arg.Name v ty !cx_
                (v, vdecl)
              ) args
            let ass0, z3value = expression !cx_ value
            let new_fn = new_skolem_fun funname fun_ty
            let inner_assumption =
              Z3Equal (
                Z3Fun (new_fn, List.map (fun (v,_) -> Z3Var v) new_vars),
                z3value
              )
            let full_assumption =
              List.fold (fun assm -> fun (_v, vdecl) ->
                Z3Forall (vdecl, assm)
              ) inner_assumption new_vars
            let ass1 = full_assumption
            Z3And (ass0, ass1), cx_update_fun funname new_fn fun_ty cx
          | IfElse (value, then_block, else_block) ->
            let ass0, z3value = expression cx value
            let ass1, cond_var =
              match z3value with
                | Z3Var name -> lit_true, name
                | _ ->
                  let v = new_skolem_var "cond" AST.Bool
                  (Z3Equal (Z3Var v, z3value), v)

            let ass2, cx_then = statement cx then_block
            let ass3, cx_else = statement cx else_block

            let ass4, cx' = merge cond_var cx cx_then cx_else

            let ass = and_list [ ass0; ass1; ass4; Z3Imply (Z3Var cond_var, ass2); Z3Imply (Z3Not (Z3Var cond_var), ass3) ]

            ass, cx'

          | IfSomeElse _ -> failwith "TwoState: TODO implement IfSomeElse"
          | Assume v ->
            let ass0, ass1 = expression cx v
            Z3And (ass0, ass1), cx
          | Assert _ -> failwith "TwoState: TODO implement Assert"

      let pre_cx = {
        cx_fun_map =
          Map.ofList (List.map (fun (fundecl : AST.FunDecl) ->
            let ty = (fundecl.Input, fundecl.Output)
            let v = new_skolem_fun fundecl.Name ty
            (fundecl.Name, (v, ty))
          ) mmd.Funs);
        cx_var_map =
          Map.ofList (List.map (fun (vardecl : AST.VarDecl) ->
            let ty = vardecl.Type
            let v = new_skolem_var vardecl.Name ty
            (vardecl.Name, (v, ty))
          ) args);
      }
      let assumptions, post_cx = statement pre_cx (content)

      let globals_only (cx: Context) : Context =
        {
          cx_fun_map = Map.ofList (List.map (fun (fundecl : AST.FunDecl) ->
            (fundecl.Name, Map.find fundecl.Name cx.cx_fun_map)
          ) mmd.Funs);
          cx_var_map = Map.empty;
        }

      {
        pre = globals_only pre_cx;
        post = globals_only post_cx;
        formula = assumptions;
        vars = !skolem_vars;
        funs = !skolem_funs;
      }

    let make_two_state_for_action (mmd : ModuleDecl<'a,'b>) (action: ActionDecl) =
      make_two_state_for_stmt mmd action.Args action.Content

    let rename_states (ts: TwoState) (name_map : Map<string, string * string>) : TwoState =
      let map_ : Map<string, string> ref = ref Map.empty
      let extra_equals = ref []
      let funs = ref ts.funs
      Map.iter (fun fun_name -> fun (pre_fun_name, post_fun_name) ->
        let cur_pre = fst (Map.find fun_name ts.pre.cx_fun_map)
        let cur_post = fst (Map.find fun_name ts.post.cx_fun_map)
        let ty = Map.find cur_pre ts.funs
        if pre_fun_name = post_fun_name then
          if cur_pre <> cur_post then
            failwith "rename_states: can't map two funs to the same fun"
          else
            map_ := Map.add cur_pre pre_fun_name !map_
            funs := Map.remove cur_pre !funs
            funs := Map.add pre_fun_name ty !funs
        else
          if cur_pre <> cur_post then
            map_ := Map.add cur_pre pre_fun_name !map_
            map_ := Map.add cur_post post_fun_name !map_

            funs := Map.remove cur_pre !funs
            funs := Map.remove cur_post !funs
            funs := Map.add pre_fun_name ty !funs
            funs := Map.add post_fun_name ty !funs
          else
            map_ := Map.add cur_pre pre_fun_name !map_
            extra_equals := (pre_fun_name, post_fun_name, ty) :: !extra_equals

            funs := Map.remove cur_pre !funs
            funs := Map.add pre_fun_name ty !funs
            funs := Map.add post_fun_name ty !funs
      ) name_map

      let map = !map_

      let rec aux (v : Z3Value) : Z3Value =
        match v with
          | Z3Const c -> Z3Const c
          | Z3Var v -> Z3Var v
          | Z3Fun (f, args) ->
              let name = if Map.containsKey f map then Map.find f map else f
              Z3Fun (name, List.map aux args)
          | Z3Equal (a, b) -> Z3Equal (aux a, aux b)
          | Z3Or (a, b) -> Z3Or (aux a, aux b)
          | Z3And (a, b) -> Z3And (aux a, aux b)
          | Z3Imply (a, b) -> Z3Imply (aux a, aux b)
          | Z3Not a -> Z3Not (aux a)
          | Z3IfElse (a, b, c) -> Z3IfElse (aux a, aux b, aux c)
          | Z3Forall (a, b) -> Z3Forall (a, aux b)
          | Z3Exists (a, b) -> Z3Exists (a, aux b)
          | Z3Hole -> Z3Hole
      
      let equal_formulas = List.map (fun (a, b, ty) -> funs_are_equal_expr a b ty) !extra_equals
      let all_formulas = (aux ts.formula) :: equal_formulas
      let full_formula = and_list all_formulas

      let map_cx (cx: Context) is_pre : Context =
        {
          cx_var_map = cx.cx_var_map;
          cx_fun_map = Map.map (fun t -> fun (_, ty) ->
              ((if is_pre then fst else snd) (Map.find t name_map), ty)
            ) cx.cx_fun_map;
        }

      {
        pre = map_cx ts.pre true;
        post = map_cx ts.post false;
        formula = full_formula;
        vars = ts.vars;
        funs = !funs;
      }

    let composeChoice (mmd: ModuleDecl<'a,'b>) (twoStates : List<TwoState>) =
      match twoStates with
        | [] -> failwith "expected at least one action"
        | [x] -> x
        | _ ->
          let state_names =
            Map.ofList (List.map (fun (fundecl : FunDecl) ->
              let fn = fundecl.Name
              let n1 = new_name fn
              let n2 = new_name fn
              if List.forall (fun ts -> cx_lookup_fun fn ts.pre = cx_lookup_fun fn ts.post) twoStates then
                (fn, (n1, n1))
              else
                (fn, (n1, n2))
            ) mmd.Funs)

          let twoStates = List.map (fun ts -> rename_states ts state_names) twoStates

          let whichActionVars = List.map (fun (action : ActionDecl) -> AST.default_var_decl (new_name ("action_" + action.Name)) AST.Bool) mmd.Actions
          let oneActionFormula = or_list (List.map (fun (var : AST.VarDecl) -> Z3Var var.Name) whichActionVars)

          let actionFormulas =
            List.map2 (fun (whichActionVar : AST.VarDecl) -> fun twoState ->
              Z3Imply (Z3Var whichActionVar.Name, twoState.formula)
            ) whichActionVars twoStates

          let fullFormula = and_list (oneActionFormula :: actionFormulas)

          let new_vars = Map.ofList (List.map (fun (whichActionVar : AST.VarDecl) -> (whichActionVar.Name, whichActionVar.Type)) whichActionVars)

          {
            pre = (List.head twoStates).pre;
            post = (List.head twoStates).post;
            formula = fullFormula;
            vars = mergeMaps (new_vars :: (List.map (fun ts -> ts.vars) twoStates))
            funs = mergeMaps (List.map (fun ts -> ts.funs) twoStates)
          }

    let composeSequentially (ts1 : TwoState) (ts2 : TwoState) =
      let ts2' = rename_states ts2 (Map.map (fun fun_name -> fun (ts2_pre, ty) ->
        let ts1_post = fst (Map.find fun_name ts1.post.cx_fun_map)
        let ts2_post = fst (Map.find fun_name ts2.post.cx_fun_map)
        if ts2_pre = ts2_post then
          (ts1_post, ts1_post)
        else
          (ts1_post, ts2_post)
      ) ts2.pre.cx_fun_map)
      {
        pre = ts1.pre;
        post = ts2'.post;
        formula = Z3And (ts1.formula, ts2'.formula);
        vars = mergeMaps [ts1.vars ; ts2'.vars];
        funs = mergeMaps [ts1.funs ; ts2'.funs];
      }

    let rec composeListSequentially (l : List<TwoState>) =
      match l with
        | [] -> failwith "expected nonempty list"
        | [x] -> x
        | x :: y ->
          let y1 = (composeListSequentially y)
          let z = composeSequentially x y1
          z
 
    let make_two_state_for_actions (mmd : ModuleDecl<'a,'b>) (actions : List<ActionDecl>) =
      let twoStates = List.map (fun action -> make_two_state_for_action mmd action) actions
      composeChoice mmd twoStates

    let make_two_state_for_k_exec (mmd: ModuleDecl<'a,'b>) init_actions (k : int) =
      composeListSequentially (List.concat
        [
          (List.map (fun (axiom:AxiomDecl) -> make_two_state_for_stmt mmd [] (Assume axiom.Formula)) mmd.Axioms);
          (List.map (fun action -> make_two_state_for_action mmd (find_action mmd action)) init_actions);
          (List.init k (fun _ -> composeChoice mmd (List.map (fun action -> make_two_state_for_action mmd action) mmd.Actions)));
        ])

    let subst (v : Z3Value) (cx : Context) =
      let rec aux (scoped: Set<string>) (v : Z3Value) : Z3Value =
        match v with
          | Z3Const c -> Z3Const c
          | Z3Var v -> if Set.contains v scoped then Z3Var v else Z3Var (cx_lookup_var v cx)
          | Z3Fun (f, args) -> Z3Fun (cx_lookup_fun f cx, List.map (aux scoped) args)
          | Z3Equal (a, b) -> Z3Equal (aux scoped a, aux scoped b)
          | Z3Or (a, b) -> Z3Or (aux scoped a, aux scoped b)
          | Z3And (a, b) -> Z3And (aux scoped a, aux scoped b)
          | Z3Imply (a, b) -> Z3Imply (aux scoped a, aux scoped b)
          | Z3Not a -> Z3Not (aux scoped a)
          | Z3IfElse (a, b, c) -> Z3IfElse (aux scoped a, aux scoped b, aux scoped c)
          | Z3Forall (a, b) -> Z3Forall (a, aux (Set.add a.Name scoped) b)
          | Z3Exists (a, b) -> Z3Exists (a, aux (Set.add a.Name scoped) b)
          | Z3Hole -> Z3Hole
      aux Set.empty v

    let skolemize formula init_vars =
      let vars = ref init_vars
      let var_map = ref Map.empty
      let rec aux modify v =
        match v with
          | Z3Const c -> Z3Const c
          | Z3Var v -> Z3Var (if Map.containsKey v !var_map then Map.find v !var_map else v)
          | Z3Fun (f, args) -> Z3Fun (f, List.map (aux modify) args)
          | Z3Equal (a, b) -> Z3Equal (aux modify a, aux modify b)
          | Z3Or (a, b) -> Z3Or (aux modify a, aux modify b)
          | Z3And (a, b) -> Z3And (aux modify a, aux modify b)
          | Z3Imply (a, b) -> Z3Imply (aux modify a, aux modify b)
          | Z3Not a -> Z3Not (aux modify a)
          | Z3IfElse (a, b, c) -> Z3IfElse (aux modify a, aux modify b, aux modify c)
          | Z3Forall (a, b) -> Z3Forall (a, aux false b)
          | Z3Exists (a, b) ->
              if modify then
                let nname = (new_name a.Name)
                vars := Map.add nname a.Type !vars
                var_map := Map.add a.Name nname !var_map
                aux modify b
              else
                Z3Exists (a, aux modify b)
          | Z3Hole -> Z3Hole
      let res = aux true formula
      (res, !vars)

    let make_sat_problem_for_k_exec
          (mmd: ModuleDecl<'a,'b>)
          (init_actions : List<string>)
          (k : int)
          (inv_neg : Z3Value) =
      let ts = make_two_state_for_k_exec mmd init_actions k

      let main_formula = WPR.simplify_z3_value (ts.formula)
      let inv_neg = WPR.simplify_z3_value (subst inv_neg ts.post)

      let vars = ts.vars
      let funs = ts.funs

      let formula, vars = skolemize main_formula vars

      (formula, inv_neg, vars, funs)

    let make_context
              (enable_unsat_core: bool)
              (mmd: ModuleDecl<'a, 'b>)
              (the_vars: Map<string, Type>)
              (the_funs: Map<string, FunType>)
              : Z3Utils.ModuleContext =
      let settings = new System.Collections.Generic.Dictionary<string,string>()
      settings.Add("unsat_core", if enable_unsat_core then "true" else "false")

      let ctx = new Microsoft.Z3.Context(settings)
      let sorts = ref Map.empty 
      let funs = ref Map.empty 
      let vars = ref Map.empty 
      for d in mmd.Types do
          match d.Infos with
          | AST.UninterpretedTypeDecl -> sorts := Map.add d.Name (ctx.MkUninterpretedSort(d.Name) :> Microsoft.Z3.Sort) (!sorts)
          | AST.EnumeratedTypeDecl strs -> sorts := Map.add d.Name (ctx.MkEnumSort(d.Name, List.toArray strs) :> Microsoft.Z3.Sort) (!sorts)

      for (name, (ty_args, ty_out)) in Map.toList the_funs do
          let domain = List.map (Z3Utils.sort_of_type ctx (!sorts)) ty_args
          let range = Z3Utils.sort_of_type ctx (!sorts) ty_out
          if List.length domain = 0 then
            funs := Map.add name (ctx.MkConstDecl(name, range)) !funs
          else
            funs := Map.add name (ctx.MkFuncDecl(name, Array.ofList domain, range)) !funs
      for (name, ty) in Map.toList the_vars do
          let range = Z3Utils.sort_of_type ctx (!sorts) ty
          funs := Map.add name (ctx.MkConstDecl(name, range)) !funs
      let z3ctx = {
        Z3Utils.ModuleContext.Context = ctx;
        Z3Utils.ModuleContext.Sorts = !sorts;
        Z3Utils.ModuleContext.Funs = !funs;
      }
      z3ctx

    let z3sat (mmd: ModuleDecl<'a, 'b>)
              (f: Z3Value)
              (inv_neg: Z3Value)
              (the_vars: Map<string, Type>)
              (the_funs: Map<string, FunType>)
              : bool =
      let z3ctx = make_context false mmd the_vars the_funs
      let ctx = z3ctx.Context
      let sorts = z3ctx.Sorts
      let funs = z3ctx.Funs

      let s = ctx.MkSolver()

      let z3e = Z3Utils.build_value z3ctx funs Map.empty (Z3And (f, inv_neg))
      s.Assert ([|z3e:?> Microsoft.Z3.BoolExpr|])

      match s.Check () with
        | Microsoft.Z3.Status.UNSATISFIABLE -> false
        | Microsoft.Z3.Status.UNKNOWN -> failwith "got unknown"
        | Microsoft.Z3.Status.SATISFIABLE ->
            //printfn "%s\n" (s.Model)
            true
        | _ -> failwith "solver returned unknown status"

    let z3unsat_core
          (s: Microsoft.Z3.Solver)
          (z3ctx: Z3Utils.ModuleContext)
          (exprs: List<Microsoft.Z3.Expr>)
          : List<Microsoft.Z3.BoolExpr> option =

      match s.Check (Seq.cast exprs) with
      //match s.Check() with
        | Microsoft.Z3.Status.UNSATISFIABLE ->
            let core = s.UnsatCore
            //Some (List.map (fun (c : Microsoft.Z3.BoolExpr) -> Map.find c.Id !map) (Seq.toList (Seq.cast core)))
            Some (Seq.toList (Seq.cast core))
        | Microsoft.Z3.Status.UNKNOWN -> failwith "got unknown"
        | Microsoft.Z3.Status.SATISFIABLE -> None
        | _ -> failwith "solver returned unknown status"
       

    let minimum_ish_core
          (mmd: ModuleDecl<'a, 'b>)
          (f: Z3Value)
          (fs: List<Z3Value>)
          (the_vars: Map<string, Type>)
          (the_funs: Map<string, FunType>)
          : List<int> =
      // based off of ivy_core.py

      let z3ctx = make_context true mmd the_vars the_funs
      let ctx = z3ctx.Context
      let sorts = z3ctx.Sorts
      let funs = z3ctx.Funs
      let s = ctx.MkSolver()
      s.Set("unsat_core", true)

      let z3e = Z3Utils.build_value z3ctx funs Map.empty f
      s.Assert ([|z3e:?> Microsoft.Z3.BoolExpr|])
      //printfn "main: %A" z3e

      let map : Map<uint32, int> ref = ref Map.empty
      let idx = ref 0
      let exprs =
        List.map (fun f ->
          let boolVar = ctx.MkConst (ctx.MkConstDecl("__clause__" + (!idx).ToString(), ctx.BoolSort :> Microsoft.Z3.Sort))
          let expr = Z3Utils.build_value z3ctx z3ctx.Funs Map.empty f
          let eq = ctx.MkEq (boolVar, expr)
          s.Assert ([|eq|])

          map := Map.add boolVar.Id !idx !map
          idx := !idx + 1
          boolVar
        ) fs

      let core = ref (Option.get (z3unsat_core s z3ctx exprs))
      let mus = ref []
      let ids : Map<uint32, bool> ref = ref Map.empty
      while !core <> [] do
        let c = List.head !core
        let new_core = List.append !mus (List.tail !core)
        match z3unsat_core s z3ctx (List.map (fun (x:Microsoft.Z3.BoolExpr) -> x :> Microsoft.Z3.Expr) new_core) with
          | None ->
              mus := List.append !mus [c]
              ids := Map.add c.Id true !ids
              core := List.tail !core
          | Some new_core ->
              core := List.filter (fun c -> not (Map.containsKey c.Id !ids)) new_core
      
      let final = List.map (fun (c : Microsoft.Z3.BoolExpr) -> Map.find c.Id !map) !mus
      final

    let is_k_invariant (mmd: ModuleDecl<'a, 'b>) init_actions (k : int) (invariant : Z3Value) =
      let init_actions = List.map fst init_actions
      let sat_prob, inv_neg, vars, funs = make_sat_problem_for_k_exec mmd init_actions k (Z3Not invariant)
      let sat_prob = WPR.simplify_z3_value sat_prob
      let inv_neg = WPR.simplify_z3_value inv_neg

      //printfn "%s\n" (Printer.z3value_to_string_pretty sat_prob)
      let is_sat = z3sat mmd sat_prob inv_neg vars funs

      //printfn (if is_sat then "SAT\n" else "UNSAT\n")
      not is_sat
      

    let k_invariant_core
        (mmd: ModuleDecl<'a, 'b>)
        init_actions
        (k : int)
        (invariant_negation : Z3Value)
        : Z3Value =
      let init_actions = List.map fst init_actions
      let sat_prob, invariant_negation', vars, funs = make_sat_problem_for_k_exec mmd init_actions k invariant_negation

      let sat_prob = WPR.simplify_z3_value sat_prob
      let invariant_negation' = WPR.simplify_z3_value invariant_negation'

      let rec get_rid_of_existentials e vars =
          match e with
          | Z3Exists (vardecl, e') ->
              let e'', vars, vardecls = get_rid_of_existentials e' vars
              let vars = Map.add vardecl.Name vardecl.Type vars
              e'', vars, (vardecl :: vardecls)
          | _ -> e, vars, []
      let rec get_conjuncts (v: Z3Value) =
          match v with
              | Z3And(a, b) -> List.append (get_conjuncts a) (get_conjuncts b)
              | _ -> [v]

      let inner, _, _ = get_rid_of_existentials invariant_negation Map.empty
      let conjuncts = get_conjuncts inner

      let inner', vars, vardecls = get_rid_of_existentials invariant_negation' vars
      let conjuncts' = get_conjuncts inner'

      let indices = minimum_ish_core mmd sat_prob conjuncts' vars funs

      List.foldBack (fun vardecl -> fun e -> Z3Forall (vardecl, e)) vardecls (Z3Not (and_list (List.map (fun idx -> conjuncts.[idx]) indices)))

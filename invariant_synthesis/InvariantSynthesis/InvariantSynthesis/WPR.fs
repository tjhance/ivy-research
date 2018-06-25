﻿module WPR

    // Thanks to https://github.com/Microsoft/ivy/blob/master/doc/decidability.md

    open MinimalAST

    type Z3Value =
        | Z3Const of ConstValue
        | Z3Var of string
        | Z3Fun of string * List<Z3Value>
        | Z3Equal of Z3Value * Z3Value
        | Z3Or of Z3Value * Z3Value
        | Z3And of Z3Value * Z3Value
        | Z3Imply of Z3Value * Z3Value
        | Z3Not of Z3Value
        | Z3IfElse of Z3Value * Z3Value * Z3Value
        | Z3Forall of VarDecl * Z3Value
        | Z3Exists of VarDecl * Z3Value
        | Z3Declare of VarDecl * Z3Value * Z3Value
        | Z3Hole // Used for contexts

    type ValueContext = Z3Value * Z3Value
    // (context for using the value, value)

    type Statement =
        | NewBlock of List<VarDecl> * List<Statement>
        | VarAssign of string * ValueContext
        | VarAssignAction of string * string * List<ValueContext>
        | FunAssign of string * List<VarDecl> * ValueContext
        | Parallel of Statement * Statement
        | Assume of ValueContext
        | Abort

    // Utility functions on types

    let replace_holes_with repl v =
        let rec aux v =
            match v with
            | Z3Const c -> Z3Const c
            | Z3Var str -> Z3Var str
            | Z3Fun (str, vs) -> Z3Fun (str, List.map aux vs)
            | Z3Equal (v1, v2) -> Z3Equal (aux v1, aux v2)
            | Z3Or (v1, v2) -> Z3Or (aux v1, aux v2)
            | Z3And (v1, v2) -> Z3And (aux v1, aux v2)
            | Z3Imply (v1, v2) -> Z3Imply (aux v1, aux v2)
            | Z3Not v -> Z3Not (aux v)
            | Z3IfElse (c,i,e) -> Z3IfElse (aux c, aux i, aux e)
            | Z3Forall (d, v) -> Z3Forall (d, aux v)
            | Z3Exists (d, v) -> Z3Exists (d, aux v)
            | Z3Declare (d, vdecl, v) -> Z3Declare (d, aux vdecl, aux v)
            | Z3Hole -> repl
        aux v
    
    let rec free_vars_of_value v =
        match v with
        | Z3Const _ -> Set.empty
        | Z3Var str -> Set.singleton str
        | Z3Fun (_, vs) -> Set.unionMany (List.map free_vars_of_value vs)
        | Z3Equal (v1, v2) | Z3Or (v1, v2) | Z3And (v1, v2) | Z3Imply (v1, v2)
            -> Set.union (free_vars_of_value v1) (free_vars_of_value v2)
        | Z3Not v -> free_vars_of_value v
        | Z3IfElse (f, v1, v2) ->
            Set.unionMany [free_vars_of_value f ; free_vars_of_value v1 ; free_vars_of_value v2]
        | Z3Forall (d, v) | Z3Exists (d, v) -> 
            let fv = free_vars_of_value v
            Set.remove d.Name fv
        | Z3Declare (d, v1, v2) ->
            let fv = free_vars_of_value v2
            let fv = Set.remove d.Name fv
            Set.union fv (free_vars_of_value v1)
        | Z3Hole -> Set.empty

    // Conversion tools

    let next_var = ref 0

    let reinit_tmp_vars () =
        next_var := 0

    let unique_name name =
        let id = !next_var
        next_var := (!next_var) + 1
        AST.make_name_unique name id

    // Utility functions

    let rename_value renaming v =
        let dico = Map.map (fun _ str -> ValueVar str) renaming
        map_vars_in_value v dico
    let rename_var renaming str =
        if Map.containsKey str renaming
        then Map.find str renaming else str

    let fail_if_ctx_depends_on ctx dependances =
        if Set.isEmpty (Set.intersect (free_vars_of_value ctx) dependances)
        then ()
        else failwith "Can't convert value to a FO Z3 value..."

    // We convert the AST to a simpler one & we rename each local variable in order for them to be unique
    let minimal_val2z3_val (m:ModuleDecl<'a,'b>) v =
        let rec aux v =
            match v with
            | ValueConst c -> (Z3Hole, Z3Const c)
            | ValueVar str -> (Z3Hole, Z3Var str)
            | ValueFun (str, vs) ->
                let (ctxs, vs) = List.unzip (List.map aux vs)
                let ctx = List.fold replace_holes_with Z3Hole (List.rev ctxs)
                (ctx, Z3Fun (str, vs))
            | ValueEqual (v1, v2) ->
                let (ctx1, v1) = aux v1
                let (ctx2, v2) = aux v2
                let ctx = replace_holes_with ctx2 ctx1
                (ctx, Z3Equal (v1, v2))
            | ValueOr (v1, v2) ->
                let (ctx1, v1) = aux v1
                let (ctx2, v2) = aux v2
                let ctx = replace_holes_with ctx2 ctx1
                (ctx, Z3Or (v1, v2))
            | ValueNot v ->
                let (ctx, v) = aux v
                (ctx, Z3Not v)
            | ValueSomeElse (d, v1, v2) ->
                let new_d = AST.default_var_decl (unique_name d.Name) d.Type
                let renaming = Map.add d.Name new_d.Name Map.empty
                let v1 = rename_value renaming v1

                let (ctx1, v1) = aux v1
                fail_if_ctx_depends_on ctx1 (Set.singleton new_d.Name)
                let (ctx2, v2) = aux v2
                let ctx2 = replace_holes_with (Z3Declare (new_d, v2, Z3Hole)) ctx2
                let none_case = Z3Imply (Z3Not (Z3Exists (new_d, v1)), ctx2)
                let some_case = Z3Forall (new_d, Z3Imply (v1, Z3Hole))
                let ctx = Z3And (some_case, none_case)
                let ctx = replace_holes_with ctx ctx1
                (ctx, Z3Var new_d.Name)
            | ValueIfElse (c,i,e) ->
                let (ctx1, c) = aux c
                let (ctx2, i) = aux i
                let (ctx3, e) = aux e
                let ctx = List.fold replace_holes_with Z3Hole [ctx3;ctx2;ctx1]
                (ctx, Z3IfElse (c,i,e))
            | ValueForall (d, v) ->
                let new_d = AST.default_var_decl (unique_name d.Name) d.Type
                let renaming = Map.add d.Name new_d.Name Map.empty
                let v = rename_value renaming v

                let (ctx, v) = aux v
                fail_if_ctx_depends_on ctx (Set.singleton new_d.Name)
                let v = Z3Forall (new_d, v)
                (ctx, v)
            | ValueInterpreted (str, _) ->
                let name = unique_name "IV"
                let d = AST.default_var_decl name (MinimalAST.find_interpreted_action m str).Output
                let ctx = Z3Forall (d, Z3Hole)
                (ctx, Z3Var name)
        aux v

    // We convert the AST to a simpler one & we rename each local variable in order for them to be unique
    let minimal_stat2wpr_stat<'a,'b> (m:ModuleDecl<'a,'b>) renaming st =
        let minimal_val2z3_val = minimal_val2z3_val m

        let packIfNecessary sts =
            if List.length sts = 1 then List.head sts
            else NewBlock ([],sts)

        let rec aux renaming st =
            match st with
            | MinimalAST.AtomicGroup sts -> List.concat (List.map (aux renaming) sts)
            | MinimalAST.NewBlock (decls, sts) ->
                let new_decls = List.map (fun (d:VarDecl) -> AST.default_var_decl (unique_name d.Name) d.Type) decls
                let renaming = List.fold2 (fun acc (od:VarDecl) (nd:VarDecl) -> Map.add od.Name nd.Name acc) renaming decls new_decls
                [NewBlock (new_decls, List.concat (List.map (aux renaming) sts))]
            | MinimalAST.VarAssign (str, v) ->
                let v = rename_value renaming v
                [VarAssign (rename_var renaming str, minimal_val2z3_val v)]
            | MinimalAST.VarAssignAction (str, action, vs) ->
                let vs = List.map (rename_value renaming) vs
                [VarAssignAction (rename_var renaming str, action, List.map minimal_val2z3_val vs)]
            | MinimalAST.FunAssign (str, hvs, v) ->
                let (vs, ds) = Interpreter.separate_hvals hvs
                let vs = List.map (rename_value renaming) vs
                let added_names = List.init (List.length vs) (fun _ -> unique_name (AST.local_name "FAV"))
                
                let new_ds = List.map (fun (d:VarDecl) -> AST.default_var_decl (unique_name d.Name) d.Type) ds
                let renaming = List.fold2 (fun acc (od:VarDecl) (nd:VarDecl) -> Map.add od.Name nd.Name acc) renaming ds new_ds
                let names = List.map (fun (d:VarDecl) -> d.Name) new_ds
                let names = Interpreter.reconstruct_hvals hvs added_names names
                let decls = List.map2 (fun n (d:VarDecl) -> AST.default_var_decl n d.Type) names (find_action m str false).Args
                
                let v = rename_value renaming v
                let add_condition acc name vcond =
                    let vcond = ValueEqual (vcond, ValueVar name)
                    ValueIfElse (vcond, acc, ValueFun (str, List.map (fun str -> ValueVar str) names))
                let v = List.fold2 add_condition v added_names vs

                [FunAssign (str,decls,minimal_val2z3_val v)]
            | MinimalAST.IfElse (vcond, sif, selse) ->
                let vcond = rename_value renaming vcond
                let sif = (Assume (minimal_val2z3_val vcond))::(aux renaming sif)
                let sif = packIfNecessary sif
                let selse = (Assume (minimal_val2z3_val (ValueNot vcond)))::(aux renaming selse)
                let selse = packIfNecessary selse
                [Parallel (sif, selse)]
            | MinimalAST.IfSomeElse (d, vcond, sif, selse) ->
                let qvar = AST.default_var_decl (unique_name (AST.local_name "ISE")) d.Type
                let renaming_qvar = Map.add d.Name qvar.Name renaming
                let vcond_qvar = rename_value renaming_qvar vcond

                let selse = aux renaming selse
                let selse = (Assume (minimal_val2z3_val (ValueForall (qvar, ValueNot vcond_qvar))))::selse
                let selse = packIfNecessary selse

                let new_d = AST.default_var_decl (unique_name d.Name) d.Type
                let renaming_d = Map.add d.Name new_d.Name renaming
                
                let sif = aux renaming_d sif
                let sif_d_assign = ValueSomeElse (qvar, vcond_qvar, ValueConst (AST.type_default_value d.Type))
                let sif = [NewBlock ([new_d], (VarAssign (new_d.Name, minimal_val2z3_val sif_d_assign))::sif)]
                let sif = (Assume (minimal_val2z3_val (ValueNot (ValueForall (qvar, ValueNot vcond_qvar)))))::sif
                let sif = packIfNecessary sif
                
                [Parallel (sif, selse)]
            | MinimalAST.Assert v ->
                let v = rename_value renaming v
                let sassert = [Assume (minimal_val2z3_val (ValueNot v));Abort]
                let sassert = packIfNecessary sassert
                [Parallel (sassert,NewBlock([],[]))]
            | MinimalAST.Assume v ->
                let v = rename_value renaming v
                [Assume (minimal_val2z3_val v)]
        packIfNecessary (aux renaming st)

    type ActionDecl = { Name: string; Args: List<VarDecl>; Output: VarDecl; Content: Statement }

    let minimal_action2wpr_action<'a,'b> (m:ModuleDecl<'a,'b>) action add_variants rename_args =
        let action = find_action m action add_variants

        let rename_decl renaming (decl:VarDecl) =
            if Map.containsKey decl.Name renaming
            then { decl with Name = Map.find decl.Name renaming } else decl

        let renaming =
            if rename_args
            then List.fold (fun acc (d:VarDecl) -> Map.add d.Name (unique_name d.Name) acc) Map.empty (action.Output::action.Args)
            else Map.empty
        let args = List.map (rename_decl renaming) action.Args
        let output = rename_decl renaming action.Output
        { Name = action.Name ; Args = args ; Output = output ; Content = minimal_stat2wpr_stat m renaming action.Content }

    // WPR

    let replace_vars dico v =
        let rec aux dico v =
            match v with
            | Z3Const c -> Z3Const c
            | Z3Var str ->
                if Map.containsKey str dico
                then Map.find str dico
                else Z3Var str
            | Z3Fun (str, vs) ->
                Z3Fun (str, List.map (aux dico) vs)
            | Z3Equal (v1, v2) ->
                Z3Equal (aux dico v1, aux dico v2)
            | Z3Or (v1, v2) ->
                Z3Or (aux dico v1, aux dico v2)
            | Z3And (v1, v2) ->
                Z3And (aux dico v1, aux dico v2)
            | Z3Imply (v1, v2) ->
                Z3Imply (aux dico v1, aux dico v2)
            | Z3Not v ->
                Z3Not (aux dico v)
            | Z3IfElse (f, v1, v2) ->
                Z3IfElse (aux dico f, aux dico v1, aux dico v2)
            | Z3Forall (d,v) ->
                let dico = Map.remove d.Name dico
                Z3Forall (d, aux dico v)
            | Z3Exists (d,v) ->
                 let dico = Map.remove d.Name dico
                 Z3Exists (d, aux dico v)
            | Z3Declare (d,v1,v2) ->
                let dico' = Map.remove d.Name dico
                Z3Declare (d, aux dico v1, aux dico' v2)
            | Z3Hole -> Z3Hole
        aux dico v

    let replace_var str repl v =
        replace_vars (Map.add str repl Map.empty) v

    let replace_fun decls str repl v =
        let rec aux v =
            match v with
            | Z3Const c -> Z3Const c
            | Z3Var str -> Z3Var str
            | Z3Fun (str', vs) ->
                if str' = str
                then
                    let dico = List.fold2 (fun acc (d:VarDecl) v -> Map.add d.Name v acc) Map.empty decls vs
                    replace_vars dico repl
                else
                    Z3Fun (str', List.map aux vs)
            | Z3Equal (v1, v2) ->
                Z3Equal (aux v1, aux v2)
            | Z3Or (v1, v2) ->
                Z3Or (aux v1, aux v2)
            | Z3And (v1, v2) ->
                Z3And (aux v1, aux v2)
            | Z3Imply (v1, v2) ->
                Z3Imply (aux v1, aux v2)
            | Z3Not v ->
                Z3Not (aux v)
            | Z3IfElse (f, v1, v2) ->
                Z3IfElse (aux f, aux v1, aux v2)
            | Z3Forall (d,v) -> Z3Forall (d, aux v)
            | Z3Exists (d,v) -> Z3Exists (d, aux v)
            | Z3Declare (d,v1,v2) -> Z3Declare (d, aux v1, aux v2)
            | Z3Hole -> Z3Hole
        aux v

    let weakest_precondition<'a,'b> (m:ModuleDecl<'a,'b>) f st =
        let rec aux f st =
            match st with
            | NewBlock (ds, sts) ->
                let names = Set.ofList (List.map (fun (v:VarDecl) -> v.Name) ds)
                let fv = free_vars_of_value f
                assert Set.isEmpty (Set.intersect fv names)
                let f = List.fold aux f (List.rev sts)
                assert Set.isEmpty (Set.difference (free_vars_of_value f) fv) // No new free variable!
                f
            | VarAssign (str, (ctx, v)) ->
                let f = replace_var str v f
                replace_holes_with f ctx
            | VarAssignAction (str, action, vs) ->
                let action = minimal_action2wpr_action m action true true
                let f = replace_var str (Z3Var action.Output.Name) f
                let f = aux f action.Content

                let assign_arg f (d:VarDecl) (ctx, v) =
                    let f = replace_var d.Name v f
                    replace_holes_with f ctx

                List.fold2 assign_arg f (List.rev action.Args) (List.rev vs)
            | FunAssign (str, ds, (ctx,v)) ->
                let f = replace_fun ds str v f
                replace_holes_with f ctx
            | Parallel (st1, st2) ->
                let f1 = aux f st1
                let f2 = aux f st2
                Z3And (f1, f2)
            | Assume (ctx, v) ->
                let f = Z3Imply (v, f)
                replace_holes_with f ctx
            | Abort -> Z3Const (AST.ConstBool false)
        aux f st
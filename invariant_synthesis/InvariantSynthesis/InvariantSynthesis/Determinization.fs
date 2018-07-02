module Determinization

    open MinimalAST


    (*
    type Value =
        | ValueConst of ConstValue
        | ValueStar of Type
        | ValueVar of string
        | ValueFun of string * List<Value>
        | ValueEqual of Value * Value
        | ValueOr of Value * Value
        | ValueNot of Value
        | ValueSomeElse of VarDecl * Value * Value
        | ValueIfElse of Value * Value * Value
        | ValueForall of VarDecl * Value
        | ValueInterpreted of string * List<Value>

    type HoleValue =
        | Hole of VarDecl
        | Val of Value

    type Statement =
        | AtomicGroup of List<Statement>
        | NewBlock of List<VarDecl> * List<Statement>
        | VarAssign of string * Value
        | VarAssignAction of string * string * List<Value>
        | FunAssign of string * List<HoleValue> * Value
        | IfElse of Value * Statement * Statement
        | IfSomeElse of VarDecl * Value * Statement * Statement
        | Assert of Value
        | Assume of Value
    *)

    let rec deter_value v : List<VarDecl> * List<Value> * Value = // new args needed, new assumptions needed, value
        let fail_if_assumptions_depend_on ass name =
            if List.exists (fun a -> Set.contains name (free_vars_of_value a)) ass
            then failwith "Can't determinize action (new fresh function must be introduced)!"

        match v with
        | ValueConst c -> ([], [], ValueConst c)
        | ValueStar t ->
            let d = AST.default_var_decl (new_tmp_var ()) t
            ([d], [], ValueVar d.Name)
        | ValueVar str -> ([], [], ValueVar str)
        | ValueFun (str, vs) ->
            let (ds, ass, vs) = deter_vs vs
            (ds, ass, ValueFun (str, vs))
        | ValueEqual (v1, v2) ->
            let (ds1, ass1, v1) = deter_value v1
            let (ds2, ass2, v2) = deter_value v2
            (ds1@ds2, ass1@ass2, ValueEqual (v1,v2))
        | ValueOr (v1, v2) ->
            let (ds1, ass1, v1) = deter_value v1
            let (ds2, ass2, v2) = deter_value v2
            (ds1@ds2, ass1@ass2, ValueOr (v1,v2))
        | ValueNot v ->
            let (ds,ass,v) = deter_value v
            (ds, ass, ValueNot v)
        | ValueSomeElse (d,vcond,velse) ->
            let new_d = AST.default_var_decl (new_tmp_var ()) d.Type
            let new_cond = map_vars_in_value vcond (Map.add d.Name (ValueVar new_d.Name) Map.empty)
            let (dscond, asscond, vcond) = deter_value new_cond
            fail_if_assumptions_depend_on asscond new_d.Name
            let (dselse, asselse, velse) = deter_value velse
            let assumption = ValueOr (vcond, ValueForall (new_d, ValueNot (vcond)))
            let v = ValueIfElse (vcond, ValueVar new_d.Name, velse)
            (dscond@[new_d]@dselse, asscond@[assumption]@asselse, v)

    and deter_vs vs =
        let aux (ds, ass, vs) v =
            let (ds', ass', v') = deter_value v
            (ds@ds', ass@ass', v'::vs)
        let (ds,ass,vs) = List.fold aux ([],[],[]) vs
        (ds, ass, List.rev vs)

    let rec deter_st st : List<VarDecl> * List<Statement> =
        match st with
        | AtomicGroup sts -> deter_sts sts
                
    and deter_sts sts =
        let aux (ds, sts) st =
            let (ds', sts') = deter_st st
            (ds@ds', sts@sts')
        List.fold aux ([],[]) sts

   // let determinize_action (md:ModuleDecl<'a,'b>) name =


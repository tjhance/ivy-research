namespace TestModule

    open AST

    type AbstractActionDecl = AbstractActionDecl<Model.TypeInfos, Model.Environment>
    type ModuleDecl = ModuleDecl<Model.TypeInfos, Model.Environment>

    module Queue =

        // AST for ivy-research/queue/queue.ivy

        let name = "Queue"

        let types : List<TypeDecl> = [{Name="incrementable.t"} ; {Name="data"}]

        let vars : List<VarDecl> =
            [
                {Name="q.next_e" ; Type=Uninterpreted("incrementable.t")} ;
                {Name="q.first_e" ; Type=Uninterpreted("incrementable.t")} ;
                {Name="q.first" ; Type=Uninterpreted("data")} ;
            ]

        let funs : List<FunDecl> =
            [
                {Name="incrementable.t.<" ; Output=Bool ;
                Input=[Uninterpreted("incrementable.t");Uninterpreted("incrementable.t")] } ;

                {Name="incrementable.succ" ; Output=Bool ;
                Input=[Uninterpreted("incrementable.t");Uninterpreted("incrementable.t")] } ;

                {Name="q.content" ; Output=Bool ;
                Input=[Uninterpreted("data");Uninterpreted("incrementable.t")] } ;

                {Name="q.spec.content_f" ; Output=Uninterpreted("data") ;
                Input=[Uninterpreted("incrementable.t")] } ;
            ]

        let relation_formula name vars =
            Equal (ValueFun(name,vars), ValueConst (ConstBool true)) ;

        let aactions : List<AbstractActionDecl> =
            [
                {
                    Name="incrementable.next" ;
                    Args=[{Name="x";Type=Uninterpreted("incrementable.t")}] ;
                    Output={Name="y";Type=Uninterpreted("incrementable.t")} ;
                    Effect=
                        (
                            fun _ env ->
                                let x = Map.find "x" env.v
                                let y =
                                    match x with
                                    | ConstInt (str, i) -> ConstInt (str, i+1)
                                    | _ -> failwith "Invalid environment"
                                { env with v = Map.add "y" y env.v }
                        ) ;
                    Assume = [] ;
                    Assert = [relation_formula "incrementable.succ" [ValueVar "x"; ValueVar "y"]] ;
                }
            ]

        let empty_formula =
            Or
                (
                    Equal (ValueVar("q.next_e"),ValueVar("q.first_e")),
                    relation_formula "incrementable.t.<" [ValueVar "q.next_e"; ValueVar "q.first_e"]
                )
        
        let empty_statement = NewBlock([],[])

        let actions : List<ActionDecl> =
            [
                {
                    Name="q.pop" ;
                    Args=[] ;
                    Output={Name="res";Type=Uninterpreted("data")} ;
                    Content=
                        (
                            NewBlock
                                (
                                    [],
                                    [
                                        Assert (Not empty_formula) ;
                                        VarAssign ("res", ExprVar "q.first") ;
                                        FunAssign ("q.content", [ExprVar "q.first";ExprVar "q.first_e"], ExprConst (ConstBool false)) ;
                                        VarAssign ("q.first_e", ExprAction("incrementable.next", [ExprVar "q.first_e"])) ;
                                        IfSomeElse
                                            (
                                                {Name="nf";Type=Uninterpreted("data")},
                                                relation_formula "q.content" [ValueVar "nf";ValueVar "q.first_e"],
                                                VarAssign ("q.first", ExprVar "nf"),
                                                empty_statement
                                            )
                                    ]
                                )
                        ) ;
                }
            ]

        let invariants =
            [
                Or
                    (
                        empty_formula,
                        Equal (ValueVar "q.first", ValueFun ("q.spec.content_f", [ValueVar "q.first_e"]))
                    )
            ]

        let queue_module : ModuleDecl =
            {
                Name=name; Types=types; Funs=funs; Vars=vars;
                AActions=aactions; Actions=actions;
                Invariants=invariants
            }
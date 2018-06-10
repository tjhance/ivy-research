namespace TestModule

    open AST

    module Queue =

        // AST for ivy-research/queue/queue.ivy

        let name = "Queue"

        let types : List<TypeDecl> = [{Name="incrementable.t"} ; {Name="data"}]

        let vars : List<VarDecl> =
            [
                {Name="q.next_e" ; Type=Uninterpreted("incrementable.t") ;
                Representation=default_representation} ;
                {Name="q.first_e" ; Type=Uninterpreted("incrementable.t") ;
                Representation=default_representation} ;
                {Name="q.first" ; Type=Uninterpreted("data");
                Representation=default_representation} ;
            ]

        let funs : List<FunDecl> =
            [
                {Name="incrementable.t.<" ; Output=Bool ;
                Input=[Uninterpreted("incrementable.t");Uninterpreted("incrementable.t")];
                Representation={DisplayName=Some "<"; Flags=Set.singleton Infix} } ;

                {Name="incrementable.succ" ; Output=Bool ;
                Input=[Uninterpreted("incrementable.t");Uninterpreted("incrementable.t")];
                Representation=default_representation} ;

                {Name="q.content" ; Output=Bool ;
                Input=[Uninterpreted("data");Uninterpreted("incrementable.t")];
                Representation=default_representation} ;

                {Name="q.spec.content_f" ; Output=Uninterpreted("data") ;
                Input=[Uninterpreted("incrementable.t")]; Representation = default_representation} ;
            ]

        let impl =
            List.concat
                [
                    Formula.binary_relation_implication "incrementable.succ" true "incrementable.t.<" true ;
                    Formula.reflexive "incrementable.succ" false "incrementable.t" ;
                    Formula.reflexive "incrementable.t.<" false "incrementable.t" ;
                    Formula.transitive "incrementable.t.<" true ;
                    Formula.transitive "incrementable.t.<" false ;
                    Formula.antisymetric "incrementable.t.<" true "incrementable.t" ;
                    Formula.antisymetric "incrementable.t.<" false "incrementable.t"
                ]

        let relation_formula name vars =
            ValueEqual (ValueFun(name,vars), ValueConst (ConstBool true)) ;

        let empty_formula =
            ValueOr
                (
                    ValueEqual (ValueVar("q.next_e"),ValueVar("q.first_e")),
                    relation_formula "incrementable.t.<" [ValueVar "q.next_e"; ValueVar "q.first_e"]
                )
        
        let empty_statement = NewBlock([],[])

        let actions : List<ActionDecl> =
            [
                {
                    Name="incrementable.next" ;
                    Args=[{Name="x";Type=Uninterpreted("incrementable.t");Representation=default_representation}] ;
                    Output={Name="y";Type=Uninterpreted("incrementable.t");Representation=default_representation} ;
                    Content=
                        (
                            NewBlock
                                (
                                    [],
                                    [
                                        VarAssign
                                            (
                                                "y",
                                                ExprSomeElse
                                                    (
                                                        {Name="y";Type=Uninterpreted("incrementable.t");Representation=default_representation},
                                                        relation_formula "incrementable.succ" [ValueVar "x"; ValueVar "y"],
                                                        ValueConst (ConstInt("incrementable.t",0))
                                                    )
                                            )
                                    ]
                                )
                        )
                } ;
                {
                    Name="q.pop" ;
                    Args=[] ;
                    Output={Name="res";Type=Uninterpreted("data");Representation=default_representation} ;
                    Content=
                        (
                            NewBlock
                                (
                                    [],
                                    [
                                        Assert (ValueNot empty_formula) ;
                                        VarAssign ("res", ExprVar "q.first") ;
                                        FunAssign ("q.content", [ExprVar "q.first";ExprVar "q.first_e"], ExprConst (ConstBool false)) ;
                                        VarAssign ("q.first_e", ExprAction("incrementable.next", [ExprVar "q.first_e"])) ;
                                        IfSomeElse
                                            (
                                                {Name="nf";Type=Uninterpreted("data");Representation=default_representation},
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
                ValueOr
                    (
                        empty_formula,
                        ValueEqual (ValueVar "q.first", ValueFun ("q.spec.content_f", [ValueVar "q.first_e"]))
                    )
            ]

        let queue_module : ModuleDecl =
            {
                Name=name; Types=types; Funs=funs; Vars=vars;
                Actions=actions; Macros=[]; Implications=impl;
                Invariants=invariants
            }
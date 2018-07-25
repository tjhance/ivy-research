namespace TestModule

    open AST

    module Queue =
        open Prime

        type ModuleDecl = ModuleDecl<Model.TypeInfos,Model.Environment>

        // AST for ivy-research/queue/queue.ivy

        let name = "Queue"

        let types : List<TypeDecl> = [{Name="incrementable.t" ; Infos=UninterpretedTypeDecl} ; {Name="data" ; Infos=UninterpretedTypeDecl}]

        let funs : List<FunDecl> =
            [
                {Name="q.next_e" ; Output=Uninterpreted("incrementable.t") ; Input = [] ;
                Representation=default_representation} ;
                {Name="q.first_e" ; Output=Uninterpreted("incrementable.t") ; Input = [] ;
                Representation=default_representation} ;
                {Name="q.first" ; Output=Uninterpreted("data"); Input = [] ;
                Representation=default_representation} ;

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
                    ValueEqual (ValueFun("q.next_e",[]),ValueFun("q.first_e",[])),
                    relation_formula "incrementable.t.<" [ValueFun ("q.next_e",[]); ValueFun ("q.first_e",[])]
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
                        ) ;
                    Module="incrementable" 
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
                                        VarAssign ("res", ExprFun ("q.first",[])) ;
                                        FunAssign ("q.content", [ExprFun ("q.first",[]);ExprFun ("q.first_e",[])], ExprConst (ConstBool false)) ;
                                        FunAssign ("q.first_e", [], ExprAction("incrementable.next", [ExprFun ("q.first_e",[])])) ;
                                        IfSomeElse
                                            (
                                                {Name="nf";Type=Uninterpreted("data");Representation=default_representation},
                                                relation_formula "q.content" [ValueVar "nf";ValueFun ("q.first_e",[])],
                                                FunAssign ("q.first", [], ExprVar "nf"),
                                                empty_statement
                                            )
                                    ]
                                )
                        ) ;
                    Module="q" 
                }
            ]

        let invariants =
            [
                {
                    Module = "q" ;
                    Formula =
                        ValueOr
                            (
                                empty_formula,
                                ValueEqual (ValueFun ("q.first",[]), ValueFun ("q.spec.content_f", [ValueFun ("q.first_e",[])]))
                            )
                }
            ]

        let exports = [("q","q.pop")]

        let queue_module : ModuleDecl =
            {
                Name=name; Types=types; Funs=funs;
                Actions=actions; Macros=[]; Implications=impl;
                Invariants=invariants; InterpretedActions=[];
                Axioms = []; Exports=exports
            }

(*
0:data ~= 1
0:data = q.first
1:data ~= q.first
0:incrementable.t ~= 1
0:incrementable.t ~= 2
0:incrementable.t = q.first_e
0:incrementable.t ~= q.next_e
1:incrementable.t ~= 2
1:incrementable.t ~= q.first_e
1:incrementable.t ~= q.next_e
2:incrementable.t ~= q.first_e
2:incrementable.t = q.next_e
q.content(1,1)
q.spec.content_f(0) = 0
q.spec.content_f(1) = 0
q.spec.content_f(2) = 0
0:incrementable.t < 1
0:incrementable.t < 2
1:incrementable.t < 2
incrementable.succ(0,1)

-----

0:data ~= 1
0:data = q.first
1:data ~= q.first
0:incrementable.t ~= 1
0:incrementable.t ~= 2
0:incrementable.t = q.first_e
0:incrementable.t ~= q.next_e
1:incrementable.t ~= 2
1:incrementable.t ~= q.first_e
1:incrementable.t ~= q.next_e
2:incrementable.t ~= q.first_e
2:incrementable.t = q.next_e
q.spec.content_f(0) = 0
q.spec.content_f(1) = 1
q.spec.content_f(2) = 0
0:incrementable.t < 1
0:incrementable.t < 2
1:incrementable.t < 2
incrementable.succ(0,1)
*)

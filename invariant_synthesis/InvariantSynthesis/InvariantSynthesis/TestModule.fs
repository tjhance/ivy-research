namespace TestModule

    open AST

    module Queue =

        // AST for ivy-research/queue/queue.ivy

        let name = "Queue"

        let types : List<TypeDecl> = [{Name="incrementable.t"} ; {Name="data"}]

        let vars : List<VarDecl> =
            [
                {Name="next_e" ; Type=Uninterpreted("incrementable.t")} ;
                {Name="first_e" ; Type=Uninterpreted("incrementable.t")} ;
                {Name="first" ; Type=Uninterpreted("data")} ;
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

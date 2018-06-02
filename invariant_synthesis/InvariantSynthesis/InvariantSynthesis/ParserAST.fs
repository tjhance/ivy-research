module ParserAST

    type Ivy_element =
        | Type of AST.TypeDecl
        | Function of AST.FunDecl
        | Variable of AST.VarDecl
        | Conjecture of AST.Formula
        | Action of AST.ActionDecl
        | Module of string * List<string> * List<Ivy_element>
        | Object of string * List<Ivy_element>
        | ObjectFromModule of string * string * List<string>

    // Convert a list of ivy elements to a global AST.ModuleDecl.
    let ivy_elements_to_ast_module elements =
        ()

    // Resolve and/or adjust references to types, functions, variables or actions
    // of an AST.ModuleDecl
    let resolve_references md =
        md

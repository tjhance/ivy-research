
type ivy_type =
    | Void
    | Bool
    | Uninterpreted of string

type type_decl = string
type fun_decl = string * ivy_type list * ivy_type * bool (* Infix? *)
type var_decl = string * ivy_type

type const_value =
    | ConstVoid
    | ConstBool of bool
    | ConstInt of string * int

type parsed_expression =
    | Const of const_value
    | VarFunAction of string * parsed_expression list
    | Equal of parsed_expression * parsed_expression
    | Or of parsed_expression * parsed_expression
    | And of parsed_expression * parsed_expression
    | Not of parsed_expression
    | Forall of var_decl * parsed_expression
    | Exists of var_decl * parsed_expression
    | Imply of parsed_expression * parsed_expression
    | SomeElse of var_decl * parsed_expression * parsed_expression


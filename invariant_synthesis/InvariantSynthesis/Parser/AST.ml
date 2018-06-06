
(* EXPRESSION *)

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

(* STATEMENT *)

type hole_expression =
    | Hole of var_decl
    | Expr of parsed_expression

type parsed_statement =
    | NewBlock of var_decl list * parsed_statement list
    | Expression of parsed_expression
    | VarAssign of string * parsed_expression
    | GeneralFunAssign of string * hole_expression list * parsed_expression
    | IfElse of parsed_expression * parsed_statement * parsed_statement
    | IfSomeElse of var_decl * parsed_expression * parsed_statement * parsed_statement
    | Assert of parsed_expression
    | Assume of parsed_expression

(* ELEMENTS *)

type action_decl = string * var_decl list * var_decl * parsed_statement
and module_decl = string * string list * parsed_element list

and parsed_element =
    | Type of type_decl
    | Function of fun_decl
    | Variable of var_decl
    | Conjecture of parsed_expression
    | AbstractAction of string * var_decl list * var_decl
    | Action of action_decl
    | Module of module_decl
    | Object of string * parsed_element list
    | ObjectFromModule of string * string * string list


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

type value =
    | ValueConst of const_value
    | ValueVar of string
    | ValueFun of string * value list
    | ValueEqual of value * value
    | ValueOr of value * value
    | ValueAnd of value * value
    | ValueNot of value
    | ValueSomeElse of var_decl * formula * value

and formula =
    | Const of bool
    | Equal of value * value
    | Or of formula * formula
    | And of formula * formula
    | Not of formula
    | Forall of var_decl * formula
    | Exists of var_decl * formula
    | Imply of formula * formula

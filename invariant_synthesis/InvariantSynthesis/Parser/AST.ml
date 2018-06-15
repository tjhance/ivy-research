open Sexplib.Std
open Ppx_sexp_conv

(* We redefine an option type, however SexpLib performs some uncompatible simplifications... *)
type 'a opt =
    | None
    | Some of 'a
    [@@deriving sexp]

(* EXPRESSION *)

type ivy_type =
    | Unknown
    | Void
    | Bool
    | Uninterpreted of string
    [@@deriving sexp]

type type_decl = string [@@deriving sexp]
type fun_decl = string * ivy_type list * ivy_type * bool (* Infix? *) [@@deriving sexp]
type var_decl = string * ivy_type [@@deriving sexp]

type const_value =
    | ConstVoid
    | ConstBool of bool
    | ConstInt of string * int
    [@@deriving sexp]

type parsed_expression =
    | Const of const_value
    | QVar of var_decl
    | VarFunMacroAction of string * parsed_expression list
    | Equal of parsed_expression * parsed_expression
    | Or of parsed_expression * parsed_expression
    | And of parsed_expression * parsed_expression
    | Not of parsed_expression
    | Forall of var_decl * parsed_expression
    | Exists of var_decl * parsed_expression
    | Imply of parsed_expression * parsed_expression
    | SomeElse of var_decl * parsed_expression * parsed_expression opt
    [@@deriving sexp]

(* STATEMENT *)

type parsed_statement =
    | NewBlock of parsed_statement list
    | NewVar of var_decl * parsed_expression opt
    | Expression of parsed_expression
    | VarAssign of string * parsed_expression
    | GeneralFunAssign of string * parsed_expression list * parsed_expression
    | IfElse of parsed_expression * parsed_statement * parsed_statement
    | IfSomeElse of var_decl * parsed_expression * parsed_statement * parsed_statement
    | Assert of parsed_expression
    [@@deriving sexp]

(* ELEMENTS *)

type action_decl = string * var_decl list * var_decl opt * parsed_statement [@@deriving sexp]
and module_decl = string * string list * parsed_element list [@@deriving sexp]

and parsed_element =
    | Type of type_decl
    | Function of fun_decl
    | Variable of var_decl
    | Macro of string * var_decl list * parsed_expression * bool (* Infix? *)
    | Definition of string * var_decl list * parsed_expression
    | Conjecture of parsed_expression
    | AbstractAction of string * var_decl list * var_decl opt
    | Implement of string * parsed_statement
    | Action of action_decl
    | After of string * parsed_statement
    | Before of string * parsed_statement
    | Module of module_decl
    | Object of string * parsed_element list
    | ObjectFromModule of string * string * string list
    [@@deriving sexp]

type parsed_elements = parsed_element list [@@deriving sexp]

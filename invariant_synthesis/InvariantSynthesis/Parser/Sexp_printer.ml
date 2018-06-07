open Sexplib.Sexp
open Str

let alphanum = Str.regexp "^[a-zA-Z0-9]+$"

let rec sexp_to_string sexp =
  match sexp with
  | Atom str ->
    if Str.string_match alphanum str 0
    then Printf.sprintf "%s" str
    else Printf.sprintf "%S" str
  | List (hd::lst) -> Printf.sprintf "[%s]" (List.fold_left (fun acc e -> Printf.sprintf "%s %s" acc (sexp_to_string e)) (sexp_to_string hd) lst)
  | List [] -> Printf.sprintf "[]"

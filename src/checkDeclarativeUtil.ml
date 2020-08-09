open Util
open GatorAst
open GatorAstPrinter
open CheckContexts

let rec helper_debug_print_lst (lst : string list) : unit =
  match lst with
  | [] -> ()
  | h :: t -> Printf.printf "%s, " h; helper_debug_print_lst t

let debug_print_lst (lst : string list) : unit =
  Printf.printf "["; helper_debug_print_lst lst; Printf.printf "]"

let rec helper_specials ((e, meta) : aexp) (lst : string list) : string list = 
  match e with
  | Val v -> lst
  | Var s -> s :: lst
  | Index (l, r) -> helper_specials_arr [l; r] lst
  | Arr args
  | FnInv (_, _, args) -> helper_specials_arr args lst
  | _ -> failwith "Not allowed to have such an expression in a declaration"

and helper_specials_arr (aexps : aexp list) (lst : string list) : string list =
  match aexps with
  | [] -> lst
  | h :: t -> 
    let head_specials = helper_specials h [] in
    helper_specials_arr (t) (List.append head_specials lst)
  
let specials (ae : aexp) : string list =
  helper_specials ae []
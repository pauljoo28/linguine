open Assoc
open Util
open GatorAst
open GatorAstPrinter
open CheckContexts
open CheckUtil

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

let bind_stip (cx : contexts) (id : string) (ml : modification list) (e : aexp) :
    contexts =
  let cx' = CheckUtil.bind cx id (Dep (specials e)) in
  let cx'' = CheckUtil.bind cx' id (Val (VALID)) in
  bind cx'' id (Stip e)


let check_valid (cx : contexts) (v : string) : unit =
  if Assoc.mem v cx._bindings.rv then
    match Assoc.lookup v cx._bindings.rv with
    | INVALID -> failwith "%s has not been updated yet"
    | VALID -> ()
  else
    ()

let rec helper_update_valid (spec_lst : string list) (valids : valid context) : unit =
  match spec_lst with
  | [] -> ()
  | h :: t -> begin
    if Assoc.mem h valids then
      match Assoc.lookup h valids with
      | INVALID -> failwith "%s has not been updated yet"
      | VALID -> helper_update_valid t valids
    else
      helper_update_valid t valids
  end

let update_valid (cx : contexts) (e : aexp) : contexts =
  let (x, t) = e in
  match x with
  | Var v -> begin
      let spec_lst = Assoc.lookup v cx._bindings.rd in
      helper_update_valid spec_lst cx._bindings.rv;
      CheckUtil.bind cx v (Val (VALID))
    end
  | _ -> failwith "Update expression can only be used with a variable"
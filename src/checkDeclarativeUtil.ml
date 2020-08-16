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

let print_valids (c : 'a context) : unit =
  debug_print_lst (Assoc.keys c)

let rec helper_specials ((e, meta) : aexp) (lst : string list) : string list = 
  match e with
  | Val v -> lst
  | Var s -> s :: lst
  | As (e', t)
  | In (e', t) -> helper_specials_arr [e'] lst
  | Index (l, r) -> helper_specials_arr [l; r] lst
  | Arr args
  | FnInv (_, _, args) -> helper_specials_arr args lst
  (* | _ -> failwith "Not allowed to have such an expression in a declaration" *)

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
  CheckUtil.bind cx'' id (Stip e)

let check_valid (cx : contexts) (v : string) : unit =
  if Assoc.mem v cx._bindings.rv then
    match Assoc.lookup v cx._bindings.rv with
    | INVALID -> failwith (v ^ " has not been updated yet")
    | VALID -> ()
  else
    ()

let rec helper_update_valid (spec_lst : string list) (valids : valid context) : unit =
  match spec_lst with
  | [] -> ()
  | h :: t ->
    if Assoc.mem h valids then
      match Assoc.lookup h valids with
      | INVALID -> failwith (h ^ " has not been updated yet")
      | VALID -> helper_update_valid t valids
    else
      helper_update_valid t valids

let update_valid (cx : contexts) (e : aexp) : contexts =
  let (x, t) = e in
  match x with
  | Var v ->
      let spec_lst = Assoc.lookup v cx._bindings.rd in
      helper_update_valid spec_lst cx._bindings.rv;
      CheckUtil.bind cx v (Val (VALID))
  | _ -> failwith "Update expression can only be used with a variable"

let rec helper_invalidate_lst (cx : contexts) (cli_lst : string list) : contexts =
  match cli_lst with
  | [] -> cx
  | h :: t ->
      let cx' = helper_invalidate cx h in
      helper_invalidate_lst cx' t

and helper_invalidate (cx : contexts) (v : string) : contexts = 
  let cx' = if (Assoc.mem v cx._bindings.rd) then CheckUtil.bind cx v (Val (INVALID)) else cx in
  let cli_lst = if (Assoc.mem v cx._bindings.rc) then Assoc.lookup v cx._bindings.rc else [] in
  helper_invalidate_lst cx' cli_lst

and helper_invalidate_arr (cx : contexts) (lst : aexp list) : contexts =
  match lst with
  | [] -> cx
  | h :: t -> 
    helper_invalidate_arr (invalidate cx h) t

and invalidate (cx : contexts) (e : aexp) : contexts =
  let (x, t) = e in
  match x with
  | Val v -> cx
  | Var v -> helper_invalidate cx v
  | Index (l, r) -> helper_invalidate_arr cx [l; r]
  | Arr args
  | FnInv (_, _, args) -> helper_invalidate_arr cx args
  | _ -> failwith "Invalidate expression can only be used with a variable"

let rec helper_add_client (cx : contexts) (spec_lst : string list) (v : string) : contexts =
  match spec_lst with
  | [] -> cx
  | h :: t ->
      if Assoc.mem h cx._bindings.rc then
        let cli_lst = Assoc.lookup h cx._bindings.rc in
        let cx' = CheckUtil.bind cx h (Cli (v :: cli_lst)) in
        helper_add_client cx' t v
      else
        let cx' = CheckUtil.bind cx h (Cli [v]) in
        helper_add_client cx' t v
      
let add_client (cx : contexts) (e : aexp) (v : string) : contexts =
  let spec_lst = specials e in
  helper_add_client cx spec_lst v
  
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

let bind_stip (cx : contexts) (id : string) (e : aexp) : contexts =
  let cx' = CheckUtil.bind cx id (Dep (specials e)) in
  let cx'' = CheckUtil.bind cx' id (Val (VALID)) in
  CheckUtil.bind cx'' id (Stip e)

let is_valid (cx : contexts) (v : string) : unit =
  if Assoc.mem v cx._bindings.rv then
    match Assoc.lookup v cx._bindings.rv with
    | INVALID -> failwith (v ^ " has not been updated yet")
    | VALID -> ()
  else
    ()

let rec helper_validate_var (spec_lst : string list) (valids : valid context) : unit =
  match spec_lst with
  | [] -> ()
  | h :: t ->
    if Assoc.mem h valids then
      match Assoc.lookup h valids with
      | INVALID -> failwith (h ^ " has not been updated yet")
      | VALID -> helper_validate_var t valids
    else
      helper_validate_var t valids

let validate_var (cx : contexts) (e : aexp) : contexts * aexp =
  let (x, t) = e in
  match x with
  | Var v ->
      let spec_lst = Assoc.lookup v cx._bindings.rd in
      helper_validate_var spec_lst cx._bindings.rv;
      CheckUtil.bind cx v (Val (VALID)), get_stip cx v
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

and invalidate_arr (cx : contexts) (lst : aexp list) : contexts =
  match lst with
  | [] -> cx
  | h :: t -> 
    invalidate_arr (invalidate_var cx h) t

and invalidate_var (cx : contexts) (e : aexp) : contexts =
  let (x, t) = e in
  match x with
  | Val v -> cx
  | Var v -> helper_invalidate cx v
  | Index (l, r) -> invalidate_arr cx [l; r]
  | Arr args
  | FnInv (_, _, args) -> invalidate_arr cx args
  | _ -> failwith "Invalidate expression can only be used with a variable"

let rec helper_bind_clients (cx : contexts) (spec_lst : string list) (v : string) : contexts =
  match spec_lst with
  | [] -> cx
  | h :: t ->
      if Assoc.mem h cx._bindings.rc then
        let cli_lst = Assoc.lookup h cx._bindings.rc in
        let cx' = CheckUtil.bind cx h (Cli (v :: cli_lst)) in
        helper_bind_clients cx' t v
      else
        let cx' = CheckUtil.bind cx h (Cli [v]) in
        helper_bind_clients cx' t v
      
let bind_clients (cx : contexts) (e : aexp) (v : string) : contexts =
  helper_bind_clients cx (specials e) v

let valid_OR (v1 : valid) (v2 : valid) : valid =
  match v1, v2 with
  | VALID, VALID -> VALID
  | _ -> INVALID
  
let rec helper_intersect_valids (keys : string list) (rv : valid context) (rv' : valid context) : valid context =
  match keys with
  | [] -> Assoc.empty
  | h :: t ->
      let v = valid_OR (Assoc.lookup h rv) (Assoc.lookup h rv') in
      Assoc.update h v (helper_intersect_valids t rv rv')
  
let intersect_valids (cx : contexts) (cx' : contexts) : contexts =
  let keys = Assoc.keys cx._bindings.rv in
  let rv' = helper_intersect_valids keys cx._bindings.rv cx'._bindings.rv in
  let _b = cx._bindings in
  let update_bindings b' = {cx with _bindings= b'} in
  update_bindings {_b with rv= rv'}

let intersect_valids_if (cx0 : contexts) (cx1 : contexts) (cx2: contexts list) (cx3 : contexts) : contexts =
  intersect_valids (List.fold_left intersect_valids cx0 (cx1 :: cx2)) cx3
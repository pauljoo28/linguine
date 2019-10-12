open CoreAst
open GatorAst
open GatorAstPrinter
open Util
open Printf
open Str
open CheckUtil
open Contexts

let rec reduce_dexp (cx: contexts) (d : dexp) : int =
    debug_print (">> reduce_dexp " ^ string_of_dexp d);
    match d with
    | DimNum n -> n
    | DimVar x -> reduce_dexp cx (get_frame cx x)
    | DimPlus (l, r) -> reduce_dexp cx l + reduce_dexp cx r

let rec unwrap_abstyp (cx: contexts) (s: string) : typ =
    debug_print ">> unwrap_abstyp";
    match get_pm cx s with
        | ParTyp (s, tl) -> debug_fail cx "unimplemented partyp unwrapping"
        | p -> p

let rec replace_abstype (c: typ Assoc.context) (t: typ) : typ =
    debug_print (">> replace_abstype " ^ string_of_typ t);
    let is_abs s = Assoc.mem s c in    
    match t with
    | ParTyp (s, tl) -> 
        if is_abs s then Assoc.lookup s c
        else ParTyp (s, List.map (replace_abstype c) tl)
    | MemberTyp (t1, t2) -> MemberTyp (replace_abstype c t1, replace_abstype c t2)
    | ArrTyp (t', d) -> ArrTyp (replace_abstype c t', d)
    | _ -> t

let rec replace_absframe (c : dexp Assoc.context) (t: typ) : typ =
    debug_print (">> replace_absframe " ^ string_of_typ t);
    let rec replace_dexp d : dexp =
        match d with
        | DimNum _ -> d
        | DimVar v -> if Assoc.mem v c then Assoc.lookup v c else failwith ("Invalid frame " ^ v)
        | DimPlus (l, r) -> DimPlus (replace_dexp l, replace_dexp r)
    in match t with
    | ArrTyp (t, d) -> ArrTyp(replace_absframe c t, replace_dexp d)
    | ParTyp (s, tl) -> ParTyp(s, List.map (replace_absframe c) tl)
    | MemberTyp (t1, t2) -> MemberTyp(replace_absframe c t1, replace_absframe c t2)
    | _ -> t

let rec is_typ_eq (cx : contexts) (t1: typ) (t2: typ) : bool =
    match (t1, t2) with
    | UnitTyp, UnitTyp
    | BoolTyp, BoolTyp
    | IntTyp, IntTyp
    | FloatTyp, FloatTyp 
    | StringTyp, StringTyp -> true
    | Literal t1, Literal t2 -> is_typ_eq cx t1 t2
    | ArrTyp (t1, d1), ArrTyp (t2, d2) -> is_typ_eq cx t1 t2 && reduce_dexp cx d1 = reduce_dexp cx d2
    | MemberTyp (t1, t2), MemberTyp(t3, t4) -> 
        is_typ_eq cx t1 t3 && is_typ_eq cx t2 t4
    | ParTyp (s1, tl1), ParTyp (s2, tl2) -> s1 = s2 && 
        (if (List.length tl1 = List.length tl2) 
        then list_typ_eq cx tl1 tl2
        else false)    
    | _ -> false

and list_typ_eq (cx : contexts) (tl1: typ list) (tl2: typ list) : bool 
    = List.fold_left2 (fun acc x y -> acc && is_typ_eq cx x y) true tl1 tl2

let delta_lookup (cx : contexts) (x : string) : typ =
    match get_frame cx x with
    | DimVar v -> ParTyp (v, [])
    | d -> FrameTyp d

let rec is_subtype (cx: contexts) (to_check : typ) (target : typ) : bool =
    debug_print (">> is_subtype " ^ (string_of_pair (string_of_typ to_check) (string_of_typ target)));
    if is_typ_eq cx to_check target then true else
    match (to_check, target) with
    | BotTyp, _ -> true
    | _, BotTyp -> false
    | _, AnyTyp -> true
    | AnyTyp, _ -> false
    | BoolTyp, GenTyp -> false
    | _, GenTyp -> true
    | AnyFrameTyp, AnyFrameTyp -> true
    | FrameTyp _, AnyFrameTyp -> true
    | GenArrTyp t1, GenArrTyp t2 -> is_subtype cx t1 t2
    | ArrTyp (t, _), GenArrTyp c -> is_subtype cx t c

    | ArrTyp (t1, d1), ArrTyp (t2, d2) ->
        reduce_dexp cx d1 = reduce_dexp cx d2 
        && is_subtype cx t1 t2
    | ParTyp (s1, tl1), ParTyp (s2, tl2) -> 
        (s1 = s2 && List.length tl1 = List.length tl2
        && is_subtype_list cx tl1 tl2)
        || is_subtype cx (typ_step cx to_check) target
    | MemberTyp (t1, t2), MemberTyp (t3, t4) ->
        is_subtype cx t1 t2 && is_subtype cx t2 t4
    | FrameTyp d1, FrameTyp d2 -> reduce_dexp cx d1 = reduce_dexp cx d1
    
    (* Type lookup cases *)
    (* Note that the primitive of a given type is the top representation of that type *)
    | Literal t, _ -> is_subtype cx target (primitive cx to_check)
    | ParTyp (s, tl), _ -> is_subtype cx (typ_step cx to_check) target
    | MemberTyp (c, o), _ -> is_subtype cx (chi_object_lookup cx c o) target
    | FrameTyp _, _ -> is_subtype cx (typ_step cx to_check) target

    | _ -> false

and is_subtype_list (cx: contexts) (l1: typ list) (l2: typ list) : bool =
    debug_print ">> check_subtype_list";
    if List.length l1 != List.length l2 then false else
    List.fold_left2 (fun acc t1 t2 -> acc || (is_subtype cx t1 t2)) false l1 l2

(* Given a parameterization and a list of types being invoked on that parameterization *)
(* Returns the appropriate concretized context if one exists *)
and match_parameterization (cx: contexts) (pml : typ list) : typ Assoc.context =
    debug_print ">> match_parameterization";
    let pmb = Assoc.bindings cx.pm in
    if List.length pmb == List.length pml
        && List.fold_left2 (fun acc (s, c) t -> is_subtype cx t c && acc) true pmb pml
    then List.fold_left2 (fun tcacc (s, c) t -> Assoc.update s t tcacc)
        Assoc.empty (Assoc.bindings cx.pm) pml
    else error cx ("Invalid parameterization provided by <" 
        ^ string_of_separated_list "," string_of_typ pml ^ ">")

(* Looks up an object 'o' definition from a coordinate scheme 'c' *)
and chi_object_lookup (cx: contexts) (c : typ) (o : typ) : typ =
    let mstr = string_of_typ (MemberTyp(c, o)) in
    debug_print (">> chi_object_lookup " ^ mstr);
    let cn, f1, on, f2 = match (c, o) with | ParTyp(c, f1), ParTyp(o, f2) -> c,f1,o,f2
        | _ -> error cx ("Invalid geometric type " ^ string_of_typ c ^ "." ^ string_of_typ o
            ^ "(Note that all geometric types must be of the form scheme<frame>.object)")
    in
    (* For now, we just check that the parameterization on c is valid; it doesn't mean anything (!) *)
    match_parameterization (with_pm cx (fst (get_scheme cx cn))) f1 |> ignore;
    tau_lookup cx (cn ^ "." ^ on) f2

(* Looks up a supertype of the given partyp *)
and tau_lookup (cx: contexts) (x: id) (pml: typ list) : typ =
    (* If the given type evaluates to a declared tag, return it *)
    (* If the return type would be a top type, resolve the dimension to a number *)
    debug_print (">> tau_lookup " ^ x ^ "<" ^ string_of_list string_of_typ pml ^ ">");
    let _,pmd,t = get_typ cx x in
    let tc = match_parameterization (with_pm cx pmd) pml in
    replace_abstype tc t

(* Steps types up a level in the subtyping tree *)
(* Returns None if given a primitive type, illegal geometric type, or external type (they have no supertype) *)
and typ_step (cx : contexts) (t : typ) : typ =
    debug_print (">> typ_step " ^ string_of_typ t);
    match t with
    | ParTyp (s, tl) -> 
        (* Looks up the supertype of s -- note that the behavior differs when inside a definition, defined by 'fail' *)
        let get_supertyp fail = (match find_typ cx s with
        | Some Tau _ -> tau_lookup cx s tl
        | Some Delta _ -> delta_lookup cx s
        | Some Chi (_, s) -> (match s with | Some p -> ParTyp(p, []) | None -> AnyTyp) 
        | _ -> fail ())
        in
        if Assoc.mem s cx.pm then get_pm cx s else
        get_supertyp (fun _ -> error cx ("Unknown type " ^ string_of_typ t))
    | MemberTyp (c, o) -> chi_object_lookup cx c o
    (* Note that literals are always the first thing to be unwrapped *)
    | Literal t' -> t'
    | ArrTyp (t', d) -> (match t' with | AnyTyp -> AnyTyp | _ -> ArrTyp (typ_step cx t', d))
    | _ -> AnyTyp

(* Produces the primitive of the given type (non-declared non-literal) *)
and primitive (cx : contexts) (t : typ) : typ =
    debug_print (">> primitive " ^ string_of_typ t);
    let rec is_primitive t' : bool =
    match t' with
    | ParTyp _ | MemberTyp _ | Literal _ -> false
    | ArrTyp (t'', _) | GenArrTyp t'' -> is_primitive t''
    | _ -> true
    in
    if is_primitive t then t else primitive cx (typ_step cx t)

let rec greatest_common_child (cx: contexts) (t1: typ) (t2: typ): typ =
    debug_print ">> greatest_common_child";
    if is_subtype cx t1 t2 then t1 else 
    if is_subtype cx t2 t1 then t2 else 
    let top = primitive cx t1 in
    if is_typ_eq cx top (primitive cx t2) then Literal top else
    error cx ("Cannot unify " ^ (string_of_typ t1) ^ " and " ^ (string_of_typ t2))

let rec least_common_parent (cx: contexts) (t1: typ) (t2: typ): typ =
    debug_print (">> least_common_parent" ^ (string_of_pair (string_of_typ t1) (string_of_typ t2)));
    if is_subtype cx t1 t2 then t2 
    else if is_subtype cx t2 t1 then t1 
    else least_common_parent cx (typ_step cx t1) t2

let least_common_parent_checked (cx : contexts) (t1: typ) (t2: typ): typ =
    match least_common_parent cx t1 t2 with
    | AnyTyp | FrameTyp _ | AnyFrameTyp
        -> error cx ("Cannot unify " ^ string_of_typ t1 ^ " and " ^ string_of_typ t2)
    | t -> t
    
(* Checks that it is possible to resolve the dimension expression under the given context *)
let rec check_dexp (cx: contexts) (d : dexp) : unit =
    match d with
    | DimNum _ -> ()
    | DimVar x -> get_frame cx x |> ignore_dexp; ()
    | DimPlus (l, r) -> check_dexp cx l; check_dexp cx r

let check_typ_valid (cx: contexts) (ogt: typ) : unit =
    let rec check_typ_valid_rec (t: typ) : unit =
        debug_print (">> check_typ_valid " ^ string_of_typ t);
        match t with
        | ParTyp (s, tl) ->
            if not (Assoc.mem s cx.pm) then
            ignore_typ (typ_step cx t);
            (* If this is an internal type, don't recurse on checking frames *)
            List.fold_left (fun _ -> check_typ_valid_rec) () tl
        | MemberTyp (c, o) ->
            ignore_typ (chi_object_lookup cx c o);
        | _ -> ()
    in check_typ_valid_rec ogt

let rec typ_erase (cx: contexts) (t : typ) : TypedAst.etyp =
    debug_print (">> typ_erase " ^ string_of_typ t);
    let d_to_c opd = match opd with
    | DimNum i -> ConstInt(i) 
    | DimVar s -> ConstVar(s)
    | _ -> error cx ("No valid concrete interpretation of " ^ string_of_typ t) in
    match t with
    | UnitTyp -> TypedAst.UnitTyp
    | BoolTyp -> TypedAst.BoolTyp
    | IntTyp -> TypedAst.IntTyp
    | FloatTyp -> TypedAst.FloatTyp
    | StringTyp -> TypedAst.StringTyp
    | ThisTyp -> debug_fail cx "Cannot erase 'this'.  Did you forget to erase it in the first pass?"
    | ArrTyp (t', d) -> TypedAst.ArrTyp (typ_erase cx t', d_to_c d) 
    | ParTyp (s, tl) ->
        let is_ext = match get_typ_safe cx s with
            | Some (ext,_,_) -> ext
            | None -> false in
        if is_ext then TypedAst.ParTyp (s, List.map (typ_erase cx) tl)
        else typ_erase cx (typ_step cx t)
    | MemberTyp _ | Literal _ -> typ_erase cx (primitive cx t)
    | AutoTyp -> error cx ("Cannot infer the type of auto")
    | AnyTyp -> TypedAst.AnyTyp
    | GenTyp -> TypedAst.GenTyp
    | BotTyp | AnyFrameTyp | FrameTyp _ | GenArrTyp _ -> debug_fail cx ("Cannot erase " ^ string_of_typ t)

let rec etyp_to_typ (e : TypedAst.etyp) : typ =
    debug_print ">> etyp_to_typ";
    match e with 
    | TypedAst.UnitTyp -> UnitTyp
    | TypedAst.BoolTyp -> BoolTyp
    | TypedAst.IntTyp -> IntTyp
    | TypedAst.FloatTyp -> FloatTyp
    | TypedAst.StringTyp -> StringTyp
    | TypedAst.ParTyp (s, tl) -> ParTyp(s, List.map etyp_to_typ tl)
    | TypedAst.ArrTyp (t, c) -> ArrTyp (etyp_to_typ t, 
        match c with | ConstInt i -> DimNum i | ConstVar v -> DimVar v)
    | TypedAst.AnyTyp -> AnyTyp
    | TypedAst.GenTyp -> GenTyp

let rec check_val (cx: contexts) (v: value) : typ = 
    debug_print (">> check_val " ^ string_of_value v);
    match v with
    | Bool b -> Literal BoolTyp
    | Num n -> Literal IntTyp
    | Float f -> Literal FloatTyp
    | StringVal s -> Literal StringTyp
    | Unit -> error cx ("Unexpected value " ^ (string_of_value v))

let exp_to_texp (cx: contexts) ((exp, t) : TypedAst.exp * typ) : TypedAst.texp = 
    debug_print (">> exp_to_texp " ^ string_of_typ t);
    exp, typ_erase cx t

(* Given a list of arguments and the arguments of a funciton 'target' *)
(* Attempts to produce a list of valid types for the parameterization of the function *)
let infer_pml (cx: contexts) (args : typ list) (target : params) : (typ list) option =
    debug_print ">> infer_pml";
    let update_inference (t : typ) (s : string) (fpm : typ Assoc.context option) : typ Assoc.context option =
        match fpm with | None -> None | Some p ->
        if Assoc.mem s p then match least_common_parent cx t (Assoc.lookup s p) with
            | AnyTyp | FrameTyp _ | AnyFrameTyp -> None
            | t' -> Some (Assoc.update s t' p)
        else Some (Assoc.update s t p)
    in
    let rec unify_param (fpm : (typ Assoc.context) option) (arg_typ : typ) (par_typ : typ) 
    : (typ Assoc.context) option =
        (* Only update our inference if we are working on an abstract type *)
        let is_abs s = Assoc.mem s cx.pm in
        let new_fpm s = if is_abs s then update_inference arg_typ s fpm else fpm in
        match arg_typ, par_typ with
        | ParTyp (_, tl1), ParTyp (s, tl2) ->
            (* Abstract params may have unspecified parameterizations provided by the arguments *)
            if List.length tl1 != List.length tl2 then new_fpm s else
            List.fold_left2 unify_param (new_fpm s) tl1 tl2
        | MemberTyp (_, t1), MemberTyp(ParTyp(s, _), t2) ->
            unify_param (new_fpm s) t1 t2
        | _, ParTyp (s, _) -> new_fpm s
        | _ -> fpm
    in
    let inferred = List.fold_left2 unify_param (Some Assoc.empty) args (List.map fst target) in
    (* Correctly sort the produced parameter list *)
    match inferred with | None -> None | Some inf ->
        (List.fold_right (fun x a -> match a with | None -> None | Some acc ->
            if Assoc.mem x inf then Some (Assoc.lookup x inf::acc) else None) (Assoc.keys cx.pm) (Some []))

let check_fn_inv (cx: contexts) (x : id) (pml: typ list) (args : (TypedAst.exp * typ) list)
: (string * TypedAst.etyp list * TypedAst.args) * typ = 
    debug_print (">> check_fn_inv " ^ x);
    let arg_typs = List.map snd args in
    (* find definition for function in phi *)
    (* looks through all possible overloaded definitions of the function *)
    let try_fn_inv (f : fn_typ) : (fn_typ * typ Assoc.context) option =
        let ml, rt, x, params, meta' = f in
        let pm = get_ml_pm cx ml in
        debug_print (">> try_fn_inv " ^ string_of_fn_typ f);
        (* This function asserts whether or not the function invocation matches the function given *)
        (* In particular, this checks whether the given function matches the given parameterization and parameters *)
        (* If it is valid, this returns (Some 'map from parameter to type'), otherwise returns 'None' *)

        (* If we have the wrong number of arguments, then no match for sure *)
        if List.length args != List.length params then None else
        (* Work out the parameter inference if one is needed *)
        let inferred_pml = 
            if Assoc.size pm == List.length pml then Some pml
            else if List.length pml == 0 then infer_pml (with_pm cx pm) arg_typs params
            else None
        in
        match inferred_pml with | None -> None | Some ipml ->
        (* Helper function for using the function parameters as they are constructed *)
        let rec apply_fpm (fpm : typ Assoc.context) (t: typ) : typ =
            let is_abs s = Assoc.mem s fpm in
            match t with
            | ParTyp (s, tl) -> 
                if is_abs s then Assoc.lookup s fpm
                else ParTyp (s, List.map (apply_fpm fpm) tl)
            | MemberTyp (t1, t2) -> MemberTyp(apply_fpm fpm t1, apply_fpm fpm t2)
            | ArrTyp (t', n) -> ArrTyp (apply_fpm fpm t', n)
            | _ -> t
        in
        (* Check that the parameterization conforms to the bounds provided *)
        let param_check = 
            debug_print ">> param_check";
            let prl = Assoc.bindings pm in
            if List.length ipml != List.length prl then None else
            List.fold_left2 (fun acc given_pm (s, t) -> 
            match acc with 
            | None -> None
            | Some fpm -> let bound = apply_fpm fpm t in 
                if is_subtype cx given_pm bound
                then Some (Assoc.update s given_pm fpm) else None)
            (Some Assoc.empty) ipml (Assoc.bindings pm)
        in
        match param_check with | None -> None | Some pm_map ->
        (* Get the parameters types and replace them in params_typ *)
        let param_typs = List.map fst params in
        let param_typs_updated = List.map (apply_fpm pm_map) param_typs in
        (* Finally, check that the arg and parameter types match *)
        if List.length arg_typs == List.length param_typs then
            option_map (fun x -> (f, x))
            (List.fold_left2 (fun acc arg param -> if (is_subtype cx arg param) then acc else None)
            param_check arg_typs param_typs_updated)
        else None
    in
    (* Check if this function should be treated as a scheme function *)
    let fn_invocated = get_functions_safe cx x in
    match List.fold_left (fun acc x -> 
        match acc, try_fn_inv x with | None, f -> f | Some _, None -> acc 
        | Some (f1,_), Some (f2,_) -> error cx ("Ambiguous choice of functions to call " 
        ^ string_of_fn_typ f1 ^ " and " ^ string_of_fn_typ f2)) None fn_invocated 
    with
    | Some (fn_found, pmt) -> 
        let ml,rt,x',_,_ = fn_found in
        (* We fold_left both to reverse the list order and to avoid writing frame type parameters *)
        let typ_erase_maybe acc (_,t) = 
            let update () = typ_erase cx t::acc in match t with | ParTyp (s, _) -> 
            (match find_typ cx s with | Some Delta _ -> acc | _ -> update()) 
            | FrameTyp _ -> acc | _ -> update()  in
        let pme = List.fold_left typ_erase_maybe [] (Assoc.bindings pmt) in
        let xr = if has_modification cx ml External then x else x' in
        (xr, pme, List.map (exp_to_texp cx) args), replace_abstype pmt rt
    | None -> error cx ("No overloaded function declaration of " ^ x
    ^ (if List.length pml > 0 then string_of_bounded_list string_of_typ "<" ">" pml else "")
    ^ " matching types " ^ string_of_bounded_list string_of_typ "(" ")" arg_typs ^ " found")

(* Checks the validity of a parameterizations, and returns the contexts updated with that pm *)
let check_parameterization (cx: contexts) (pm: parameterization) : contexts =
    debug_print (">> check_parameterization " ^ string_of_parameterization pm);
    let check_parameter found (s, t) =
        if Assoc.mem s found then error cx ("Duplicate parameter `" ^ s)
        else check_typ_valid (with_pm cx found) t;
        Assoc.update s t found
    in
    ignore_typ_context (List.fold_left check_parameter Assoc.empty (Assoc.bindings pm));
    with_pm cx pm

let update_psi (cx: contexts) (f : fn_typ) : contexts =
    (* Update psi, raising errors in case of a duplicate *)
    (* If the given type is not valid in psi, psi is returned unmodified *)
    (* Will raise a failure if a non-concrete vartyp is used *)
    let ml,rt,id,pr,_ = f in
    let pm = get_ml_pm cx ml in
    debug_print (">> update_psi " ^ string_of_fn_typ f);
    let target = rt in
    if List.length pr != 1 then cx else
    let start = fst (List.hd pr) in
    let is_valid (t: typ) : bool = match t with MemberTyp _ -> true | _ -> false in
    if not (is_valid start) || not (is_valid target) then cx else
    let as_geo_typ (t : typ) : (string * string) option =
        match t with
        | MemberTyp (ParTyp(c, _), ParTyp(o, _)) -> Some (c,o)
        | _ -> None
    in
    match as_geo_typ start with | None -> cx | Some (c1,o1) ->
    match as_geo_typ target with | None -> cx | Some (c2,o2) ->
    let start_string = string_of_typ start in
    let to_add = (target, (id, Assoc.values pm)) in
    if List.mem Canon ml then
        if Assoc.mem start_string cx.ps then 
        (let start_fns = Assoc.lookup start_string cx.ps in
            if (List.fold_left (fun acc (lt, (_, _)) -> acc ||
                    is_typ_eq cx lt target)) false start_fns
            then error cx ("Duplicate transformation for " ^ 
                start_string ^ "->" ^ string_of_typ target ^
                " in the declaration of " ^ string_of_fn_typ f)
            else with_ps cx (Assoc.update start_string (to_add :: start_fns) cx.ps)
        )
        else with_ps cx (Assoc.update start_string [to_add] cx.ps)
    else cx

(* Type check parameter; check parameter typ validity *)
(* Returns gamma *)
let check_param (cx: contexts) (t, id: typ * string) : contexts = 
    debug_print ">> check_param";
    check_typ_valid cx t;
    bind cx id (Gamma t)
    
(* Get list of parameters from param list *)
(* Returns gamma *)
let check_params (cx: contexts) (pl : params) : contexts * TypedAst.params = 
    debug_print ">> check_params";
    let cx' = List.fold_left check_param cx pl in 
    let p = (List.map (fun (t, x) -> typ_erase cx t, x) pl) in 
    cx', p

let check_index_exp (cx : contexts) (t1 : typ)  (t2 : typ) : typ =
    match (primitive cx t1), (primitive cx t2) with
    | ArrTyp (t, _), IntTyp -> t
    | _ -> error cx ("Expected array and integer for indexing, got " 
        ^ string_of_typ t1 ^ " and " ^ string_of_typ t2)

let check_as_exp (cx: contexts) (start: typ) (target : typ) : typ =
    ignore_typ (least_common_parent_checked cx start target); target

(* Super expensive.  We're essentially relying on small contexts *)
let check_in_exp (cx: contexts) (start_exp: aexp) (start: typ) (target: typ) : aexp = 
    debug_print ">> check_in_exp";
    let rec psi_path_rec (to_search: (typ * aexp) Queue.t) (found: typ list) : aexp =
        let search_phi (tl: typ) (ps_lst : (typ * fn_inv) list) : (typ * fn_inv) list =
            (* This function searches phi for canonical abstract functions that map from the given type *)
            (* A list of the types these functions map with the inferred type parameters is returned *)
            (* If multiple functions are possible, then ambiguities are resolved with the following priorities *)
            (* 1. Minimize upcasting requirements (actually handled by use of this function) *)
            (* 2. Minimize number of type parameters *)
            (* 3. Minimize constraint bounds *)
            let rec search_fns (fns : fn_typ list) : (typ * (id * typ list * typ list)) list =
                match fns with
                | [] -> []
                | (ml, rt, id, params, _)::t ->
                    let pm = get_ml_pm cx ml in
                    let cxf = with_pm cx pm in
                    if not (has_modification cx ml Canon) then search_fns t else
                    let pt = match params with | [pt,_] -> pt 
                    | _ -> debug_fail cx ("function " ^ id ^ " with non-one argument made canonical") in
                    match infer_pml cxf [tl] params with | None -> search_fns t | Some pml ->
                    let pr1 = List.map snd (Assoc.bindings pm) in
                    let rtr = replace_abstype (match_parameterization (with_pm cxf pm) pml) rt in
                    let ptr = replace_abstype (match_parameterization (with_pm cxf pm) pml) pt in
                    let fail id2 s = error cxf ("Ambiguity between viable canonical functions " 
                        ^ id ^ " and " ^ id2 ^ " (" ^ s ^ ")") in
                    let compare_parameterizations (acc : bool option) t1 t2 : bool option = 
                        let result = is_subtype cxf t1 t2 in match acc with | None -> Some result
                        | Some b -> if b = result then acc else error cxf
                        ("Ambiguous constraint ordering between " ^ string_of_typ t1
                        ^ " and " ^ string_of_typ t2)
                    in
                    if not (is_subtype cxf tl ptr) then search_fns t else
                    match rtr with
                    | MemberTyp _ -> let rec_result = search_fns t in
                        if List.fold_left (fun acc (rt, _) -> is_typ_eq cx rt rtr || acc) false rec_result then
                            List.map (fun (rt, (id2, pml2, pr2)) -> 
                            if (List.length pr1 = List.length pr2) && (List.length pr1 = 0) then
                            fail id2 ("duplicate concrete paths from " ^ string_of_typ tl ^ " to " ^ string_of_typ rtr)
                            else if not (is_typ_eq cxf rt rtr) then (rt, (id2, pml2, pr2))
                            else if List.length pr1 < List.length pr2 then (rt, (id, pml, pr1))
                            else if List.length pr2 < List.length pr1 then (rt, (id2, pml2, pr2))
                            else if (match List.fold_left2 compare_parameterizations None pr1 pr2 with
                                | None -> debug_fail cxf "Unexpected concrete function type duplicates in phi" 
                                | Some b -> b) then (rt, (id2, pml2, pr2))
                            else (rtr, (id, pml, pr1))) rec_result
                        (* No duplicate type result found, just add this function to the list *)
                        else (rtr, (id, pml, pr1)) :: rec_result
                    | _ -> debug_fail cxf ("Canonical function " ^ id ^ " resulted in type "
                        ^ string_of_typ rtr ^ ", while canonical functions should always result in a coordtyp")
            in
            let rec search_phi_rec (fns : (string * fn_typ list) list) =
            match fns with
            | [] -> List.map (fun (t, (x, y)) -> (t, (x, y, []))) ps_lst 
            | (_, fs) :: t ->
                search_fns fs @ search_phi_rec t
            in
            (* TODO: using _bindings here is super janky, but it's hard to fix rn, so... *)
            List.map (fun (t, (x, y, z)) -> (t, (x, y))) (search_phi_rec (Assoc.bindings cx._bindings.p))
        in
        let rec psi_lookup_rec (nt: typ) : (typ * fn_inv) list =
            (* NOTE: paths which would send to a type with more than 
             * 5 generic levels are rejected to avoid infinite spirals *)
            let rec check_typ_ignore (t: typ) (count: int) : bool =
                if count > 5 then true else
                match t with
                | MemberTyp (_, ParTyp (_, tl)) -> List.fold_left (fun acc t -> acc || check_typ_ignore t (count + 1)) false tl
                | _ -> false
            in
            if check_typ_ignore nt 0 then [] else
            let s_lookup = string_of_typ nt in
            let ps_lst = if Assoc.mem s_lookup cx.ps then Assoc.lookup s_lookup cx.ps else [] in
            let to_return = search_phi nt ps_lst in
            let next_step = match nt with | MemberTyp _ -> typ_step cx nt | _ -> nt in
            match next_step with
            | MemberTyp _ -> 
                to_return @ psi_lookup_rec next_step
            | _ -> to_return
        in 
        let rec update_search_and_found (vals: (typ * fn_inv) list) (e: aexp) : typ list =
            match vals with
            | [] -> found
            | (t1, (v, pml))::t -> 
                if List.fold_left (fun acc t2 -> acc || is_typ_eq cx t1 t2) false found 
                then update_search_and_found t e else 
                (* Erase the specific invocation found above for future typechecking *)
                (* This is a hack that can probably get removed in favor of not typechecking the (already found) result *)
                let v' = String.sub v 0 (String.rindex v '_') in
                let e' = FnInv (v', pml, [e]), snd e in
                (* Note the update to the stateful queue *)
                (Queue.push (t1, e') to_search;  t1 :: update_search_and_found t e)
        in
        let nt, e = if Queue.is_empty to_search 
            then error cx ("Cannot find a path from " ^
                string_of_typ start ^ " to " ^ string_of_typ target)
            else Queue.pop to_search 
        in 
        (* We use the 'with_strictness' version to avoid throwing an exception *)
        if is_subtype cx nt target then e
        else psi_path_rec to_search (update_search_and_found (psi_lookup_rec nt) e)
    in	
    if string_of_typ start = string_of_typ target then start_exp else
	let q = Queue.create () in Queue.push (start, start_exp) q;
	psi_path_rec q []

let rec check_aexp (cx: contexts) ((e, meta) : aexp) : TypedAst.exp * typ =
    check_exp (with_meta cx meta) e

and check_exp (cx: contexts) (e : exp) : TypedAst.exp * typ = 
    debug_print ">> check_exp";
    match e with
    | Val v -> (TypedAst.Val v, check_val cx v)
    | Var v -> "\tVar "^v |> debug_print; TypedAst.Var v, get_var cx v
    | Arr a -> check_arr cx a
    | As (e', t) -> let er, tr = check_aexp cx e' in er, check_as_exp cx tr t
    | In (e', t) -> let _, tr = check_aexp cx e' in 
        check_aexp cx (check_in_exp cx e' tr t)
    | Index (l, r) -> 
        let el = check_aexp cx l in
        let er = check_aexp cx r in
        TypedAst.Index(exp_to_texp cx el, exp_to_texp cx er), check_index_exp cx (snd el) (snd er)
    | FnInv (x, pr, args) -> 
        let (a, b, c), t = check_fn_inv cx x pr (List.map (check_aexp cx) args) in
        TypedAst.FnInv (a, b, c), t
        
and check_arr (cx: contexts) (a : aexp list) : TypedAst.exp * typ =
    debug_print ">> check_arr";
    let a' = List.map (check_aexp cx) a in
    TypedAst.Arr(List.map (exp_to_texp cx) a'),
    Literal (ArrTyp (List.fold_left (fun acc (_,t) -> least_common_parent_checked cx acc t) BotTyp a'
        , DimNum (List.length a)))

(* Updates Gamma and Psi *)
let rec check_acomm (cx: contexts) ((c, meta): acomm) : contexts * TypedAst.comm =
    check_comm (with_meta cx meta) c

(* Updates Gamma and Psi *)
and check_comm (cx: contexts) (c: comm) : contexts * TypedAst.comm =
    debug_print (">> check_comm " ^ string_of_comm c);
    match c with
    | Skip -> cx, TypedAst.Skip
    | Print e -> (
        let (e, t) = exp_to_texp cx (check_aexp cx e) in 
        match t with
        | UnitTyp -> error cx ("Print function cannot print void types")
        | _ -> cx, TypedAst.Print (e, t)
    )
    | Exp e -> cx, TypedAst.Exp(exp_to_texp cx (check_aexp cx e));
    | Decl (t, s, e) -> 
        check_typ_valid cx t; 
        let result = check_aexp cx e in
        let t' = (match t with 
            | AutoTyp -> (let t' = snd result in
                match t' with
                | FrameTyp _ | AnyFrameTyp -> error cx ("Cannot write " ^ string_of_typ t' ^ " to auto")
                | Literal _ | BotTyp -> error cx ("Cannot infer the type of " ^ string_of_aexp e)
                | _ -> t')
            | _ -> t) in
        check_assign cx t' s (snd result);
        bind cx s (Gamma t'), TypedAst.Decl (typ_erase cx t', s, (exp_to_texp cx result))
    | Assign (s, e) ->
        let t = get_var cx s in
        let result = check_aexp cx e in
        check_assign cx t s (snd result);
        cx, TypedAst.Assign (s, (exp_to_texp cx result))
    | AssignOp (s, b, e) -> 
        let cx', c' = check_acomm cx 
            (Assign (s, (FnInv(b, [], [Var s, snd e; e]), cx.meta)), cx.meta) in
        (match c' with
        | TypedAst.Assign (_, (TypedAst.FnInv (_, _, [_, st; e]), _)) -> 
            cx', TypedAst.AssignOp((s, st), b, e)
        | _ -> debug_fail cx "Assign must return an assign?")
    | If ((b, c1), el, c2) ->
        let check_if b c =
            let er = (check_aexp cx b) in
            let _, cr = check_comm_lst cx c in
            (match snd er with 
            | BoolTyp -> ((exp_to_texp cx er), cr)
            | _ -> error cx ("Expected boolean expression for if condition"))
        in
        let c2r = (match c2 with | Some e -> Some (snd (check_comm_lst cx e)) | None -> None) in
        cx, TypedAst.If (check_if b c1, List.map (fun (b, c) -> check_if b c) el, c2r)
    | For (c1, b, c2, cl) ->
        let cx', c1r = check_acomm cx c1 in
        let br, brt = check_aexp cx' b in
        let btexp = exp_to_texp cx (br, brt) in
        let cx'', c2r = check_acomm cx' c2 in
        cx, TypedAst.For (c1r, btexp, c2r, (snd (check_comm_lst cx'' cl)))
    | Return e ->
        cx, TypedAst.Return(option_map (exp_to_texp cx |- check_aexp cx) e)

(* Updates Gamma and Psi *)
and check_comm_lst (cx: contexts) (cl : acomm list) : contexts * TypedAst.comm list = 
    debug_print ">> check_comm_lst";
    match cl with
    | [] -> cx, []
    | h::t -> let cx', c' = check_acomm cx h in
        let cx'', cl' = check_comm_lst cx' t  in 
        cx'', c' :: cl'

(* Updates Gamma *)
and check_assign (cx: contexts) (t: typ) (s: string) (etyp : typ) : unit =
    debug_print (">> check_assign " ^ string_of_typ t ^ " " ^ s ^ " assigned " ^ string_of_typ etyp);
    (* Check that t, if not a core type, is a registered tag *)
    let rec check_tag (t: typ) : unit =
        match t with
        | ParTyp _ -> typ_step cx t |> ignore_typ; ()
        | _ -> ()
    in
    check_tag t;
    if is_subtype cx etyp t then ()
    else error cx ("Mismatched types for var decl for " ^ s ^
        ": expected " ^ string_of_typ t ^ ", found " ^ string_of_typ etyp)

(* Helper function for type checking void functions. 
 * Functions that return void can have any number of void return statements 
 * anywhere. *)
let check_void_return (cx : contexts) (c: acomm) : unit =
    debug_print ">> check_void_return";
    match c with
    | (Return Some _, _) -> error cx ("Void functions cannot return a value")
    | _ -> ()

let check_return (cx: contexts) (t: typ) (c: acomm) : unit = 
    debug_print ">> check_return";
    match t,c with
    | UnitTyp, (Return None, meta) -> ()
    | _, (Return None, meta) -> error (with_meta cx meta) ("Expected a return value instead of void")
    | UnitTyp, (Return Some _, meta) -> error (with_meta cx meta) ("Void functions cannot return a value")
    | _, (Return Some r, meta) -> (
        let cx' = with_meta cx meta in
        let _, rt = check_aexp cx' r in
        (* raises return exception of given boolean exp is false *)
        if is_subtype cx' rt t then () 
        else error cx' ("Mismatched return types, expected: " ^ 
        string_of_typ t ^ ", found: " ^ string_of_typ rt))
    | _ -> ()

(* Updates Tau with new typing information *)
let check_typ_decl (cx: contexts) (x : string) (ext,pm,t : tau) : contexts =
    debug_print ">> check_tag_decl";
    let rec check_valid_supertype (t: typ) : typ =
        match t with
        | AnyTyp
        | BoolTyp
        | IntTyp
        | FloatTyp
        | StringTyp -> t
        | ArrTyp (t', _) -> check_valid_supertype t'
        | ParTyp (s, pml) -> 
            let _,tpm,_ = get_typ cx s in
            let pmb = Assoc.bindings tpm in
            if List.length pmb == List.length pml
            then (List.fold_left2 (fun acc (s, c) t -> if is_subtype cx t c then () else
                error cx ("Invalid constraint used for parameterization of " ^ s))
                () (Assoc.bindings tpm) (List.map check_valid_supertype pml); t)
            else error cx ("Invalid number of parameters provided to parameterized type " ^ s)
        | _ -> error cx ("Invalid type declaration " ^ string_of_typ t)
    in
    check_valid_supertype t |> ignore_typ;
    bind cx x (Tau (ext,pm,t))

(* Updates Phi, and internal calls update gamma and psi *)
let check_fn_decl (cx: contexts) (f : fn_typ) : 
contexts * TypedAst.params * TypedAst.parameterization =
    let ml,rt,id,pl,meta = f in
    let pm = get_ml_pm cx ml in
    debug_print (">> check_fn_decl : " ^ id ^ string_of_parameterization pm);
    let cx' = check_parameterization cx pm in
    let cx'',pr = check_params cx' pl in
    check_typ_valid cx' rt;
    let pme = Assoc.create (List.map (fun (s, c) -> (s, typ_erase cx c)) (Assoc.bindings pm)) in
    (* Don't return the parameterization used here *)
    cx'', pr, pme

(* Updates mu, phi, and psi from underlying calls *)
let check_fn (cx: contexts) (f, cl: fn) 
: contexts * TypedAst.fn = 
    let ml,rt,id,pl,meta = f in
    debug_print (">> check_fn : " ^ id);
    (* update phi with function declaration *)
    let cx', tpr, tpm = check_fn_decl cx f in
    (* Note that we don't use our updated phi to avoid recursion *)
    let cx'', cl' = check_comm_lst cx' cl in
    let id', cxr = bind_function (reset cx'' cx CGamma) f in
    (* check that the last command is a return statement *)
    (* TODO: might want to check that there is exactly one return statement on each branch *)
    List.iter (check_return cx'' rt) cl; 
    with_pm cxr Assoc.empty, ((typ_erase cx' rt, id', tpm, tpr), cl')

(* Type check global variable *)
(* Updates gamma *)
let check_global_variable (cx: contexts) (ml, sq, t, id, e: global_var) 
: contexts * TypedAst.global_var =
    debug_print ">> check_global_variable";
    check_typ_valid cx t;
    let e' = option_map (fun x -> check_aexp cx x) e in
    (match e' with | Some (_,te) -> check_assign cx t id te | None -> ());
        bind cx id (Gamma t),
        (sq, typ_erase cx t, id, option_map (fun x -> exp_to_texp cx x) e')

let check_frame (cx : contexts) ((id, d) : frame) : contexts =
    debug_print (">> check_frame " ^ id);
    check_dexp cx d; bind cx id (Delta d)

let rewrite_scheme_typ (cx : contexts) (scheme : id) : typ -> typ =
    let f (st : id) (spm : typ list) (t : typ) : typ = 
        let rec map_typ_rec t' = 
        match t' with 
        | ParTyp (s, pm) -> 
            let pm' = List.map map_typ_rec pm in
            (match get_typ_safe cx s with 
            | Some _ -> ParTyp(s, pm')
            | None -> 
                (match get_typ_safe cx (st ^ "." ^ s) with 
                | Some _ -> 
                    MemberTyp(ParTyp (st, spm), ParTyp(s, pm'))
                | None -> error cx ("Unknown type " ^ string_of_typ t)))
        | MemberTyp(ThisTyp, t2) -> MemberTyp (ParTyp(st, spm), t2)
        | MemberTyp(ParTyp(s, pm), t2) -> 
            if s = "this" then MemberTyp (ParTyp(st, spm), t2) else t
        | MemberTyp(t1, t2) -> MemberTyp (map_typ_rec t1, map_typ_rec t2)
        | ArrTyp (tl, a) -> ArrTyp(map_typ_rec tl, a)
        | GenArrTyp t'' -> GenArrTyp(map_typ_rec t'')
        | _ -> t' in
        map_typ_rec t
    in match get_scheme cx scheme with
    | pm,None -> f scheme []
    | pm,Some _ -> f scheme (List.map (fun s -> ParTyp (s, [])) (Assoc.keys pm))

let rewrite_scheme_fn_inv (cx : contexts) (scheme : id) (s : string) : string =
    match find_exp cx s with
    | Some _ -> s
    | None -> (match find_typ cx s with 
        | Some _ -> s
        | None -> scheme ^ "." ^ s)

(* Updates tau or phi with the prototype element being checked *)
let check_prototype_element (cx : contexts) (p : string) (pe : prototype_element) : contexts =
    debug_print (">> check_prototype_element " ^ string_of_prototype_element pe);
    match pe with
    | ProtoObject (ml, id, t) -> 
        let pm = get_ml_pm cx ml in
        bind cx (p ^ "." ^ id) (Tau (false, pm, match t with | Some t' -> t' | None -> AnyTyp))
    (* We don't actually generate erased prototype functions, just typecheck them *)
    | ProtoFn f -> let _,rt,_,pr,_ = f in
        check_typ_valid cx rt; List.fold_left (fun acc -> check_typ_valid cx |- fst) () pr;
        snd (bind_function cx (rename_fn (fun x -> p ^ "." ^ x) f))
let check_aprototype_element cx p ape : contexts = 
    let pe', meta = map_aprototype_element cx (rewrite_scheme_fn_inv cx p)
        (fun x -> x) (rewrite_scheme_typ cx p) ape in
    check_prototype_element (with_meta cx meta) p pe'

(* Updates tau or phi with the coordinate scheme element being checked *)
(* We assume that  *)
let check_coordinate_element (cx : contexts) (c: string) (ce : coordinate_element) : 
    contexts * TypedAst.fn option =
    debug_print (">> check_coordinate_element " ^ string_of_coordinate_element ce);
    let cpm,proto = get_scheme cx c in
    let proto = match proto with | Some s -> s | _ ->
        error cx ("Coordinate scheme " ^ c ^ " does not extend a prototype")
    in
    match ce with
    | CoordObjectAssign (ml, id, t) -> 
        (* Check that the object is declared in the underlying prototype *)
        let _,s,_ = get_typ cx (proto ^ "." ^ id) in
        let fl = Assoc.bindings(get_ml_pm cx ml) in
        let s = Assoc.keys s in
        if List.length s != List.length fl then
            error cx (id ^ " does not have the same number of frame parameterizations as in " ^ proto);
        (* Check that the object has a resolvable type *)
        let pm = Assoc.create (List.map (fun x -> x) fl) in
        check_typ_valid (with_pm cx pm) t;
        bind cx (c ^ "." ^ id) (Tau (false, pm, t)), None
    | CoordFn fn ->
        let f, cl = fn in
        let ml, rt, id, pr, meta = f in
        let pm = get_ml_pm cx ml in
        let cxpm = with_pm cx pm in
        (* Check associated functions in the prototype to see if any match *)
        let fns = get_functions_safe cx (proto ^ "." ^ id) in
        let has_binding = 
            (* If there's no expected declaration, then this is an internal function *)
            List.length fns = 0 ||
            List.fold_left (fun acc (_,prt,_,ppr,_) -> 
            acc || (is_subtype cxpm rt prt &&
            is_subtype_list cxpm (List.map fst pr) (List.map fst ppr)))
            false fns
        in
        if not has_binding then error cx 
            ("The type of function " ^ c ^ "." ^ id ^ " does not match any prototype definition");
        (* Naming hack to make functions that aren't in the prototype 'internal' *)
        let fn' = if List.length fns = 0 then (rename_fn (fun x -> c ^ "." ^ x) f),cl else fn in
        let cx', tfn = check_fn cxpm fn' in
        cx', Some tfn
let check_acoordinate_element cx c ace : contexts * TypedAst.fn option =
    let ce',meta = map_acoordinate_element cx (rewrite_scheme_fn_inv cx c)
    (fun x -> x) (rewrite_scheme_typ cx c) ace in
    check_coordinate_element (with_meta cx meta) c ce'

(* Returns the context with a checked prototype *)
let check_prototype (cx: contexts) ((id, p) : prototype) : contexts =
    debug_print (">> check_prototype " ^ id);
    let cx' = bind cx id (Chi (Assoc.empty, None)) in
    List.fold_left (fun acc (pe, meta) -> 
        check_aprototype_element acc id (pe, meta)) cx' p

(* Returns the context with a checked coordinate scheme *)
let check_coordinate (cx: contexts) ((ml,id,p,ce) : coordinate) : contexts * TypedAst.fn list =
    debug_print (">> check_coordinate " ^ id);
    let pm = get_ml_pm cx ml in
    let cx' = bind cx id (Chi (pm, Some p)) in
    List.fold_left (fun (cx', fnl) (ce, meta) -> let cx'', tf = check_acoordinate_element cx' id (ce, meta) in
        cx'', (match tf with None -> fnl | Some f -> f::fnl)) (cx', []) ce

(* Check that there is a void main() defined *)
let check_main_fn (cx: contexts) : unit =
    debug_print ">> check_main_fn";
    let main_fns = get_functions cx "main" in
    if List.length main_fns != 1 then error cx ("Multiple declarations of main") else
    let ml, rt, id, pr, meta = List.hd main_fns in 
    let pm = get_ml_pm cx ml in
    debug_print (">> check_main_fn_2" ^ (string_of_list string_of_param pr) ^ (string_of_parameterization pm));
    if (List.length pr) > 0 || (Assoc.size pm) > 0 then error cx ("Cannot provide parameters to main") else
    match rt with
        | UnitTyp -> ()
        | _ -> raise (TypeException "Expected main function to return void")

let rec check_term (cx: contexts) (t: term) 
: contexts * TypedAst.prog * TypedAst.global_vars =
    match t with
    | Using s -> check_exprog (get_prog cx s) cx
    | Prototype p -> check_prototype cx p, [], []
    | Coordinate c -> let cx',tf = check_coordinate cx c in
        cx', tf, []
    | Frame f -> check_frame cx f, [], []
    | Typ (ml, id, t) ->
        let pm = get_ml_pm cx ml in
        let ext = has_modification cx ml External in
        check_typ_decl cx id (ext, pm, t), [], []
    | GlobalVar gv -> let (cx', gv') = check_global_variable cx gv in
        cx', [], [gv']
    | Fn f -> let (cx', f') = check_fn cx f in
        cx', [f'], []
    
and check_aterm (cx: contexts) ((t, meta): aterm) 
: contexts * TypedAst.prog * TypedAst.global_vars =
    check_term (with_meta cx meta) t

(* This might end up being really bad -- there's no scoping management on external files *)
and check_exprog (tl: prog) (cx : contexts) :
contexts * TypedAst.prog * TypedAst.global_vars =
    let cx', f, gv = List.fold_left (fun acc t -> let cx', f', gv' = check_aterm (tr_fst acc) t in
    (cx', f'@(tr_snd acc), gv'@(tr_thd acc)))
    (cx, [], []) tl in
    cx', List.rev f, List.rev gv

let rec check_term_list (tl: prog) (externs: prog Assoc.context) :
contexts * TypedAst.prog * TypedAst.global_vars =
    debug_print ">> check_global_var_or_fn_lst";
    (* Annoying bootstrapping hack *)
    let cx, f, gv = List.fold_left (fun acc t -> let cx', f', gv' = check_aterm (tr_fst acc) t in
        (cx', f'@(tr_snd acc), gv'@(tr_thd acc)))
        (init (snd (List.hd tl)) externs, [], []) tl in
    cx, List.rev f, List.rev gv

(* Returns the list of fn's which represent the program 
 * and params of the void main() fn *)
let check_prog (tl: prog) (externs: prog Assoc.context) : TypedAst.prog * TypedAst.global_vars =
    debug_print ">> check_prog";
    let cx, typed_prog, typed_gvs = check_term_list tl externs in
    check_main_fn cx;
    debug_print "===================";
    debug_print "Type Check Complete";
    debug_print "===================\n";
    typed_prog, typed_gvs

(* Searches the program for files which need to be loaded *)
(* If we have any duplicate names, throws an exception to avoid cycles *)
let rec search_prog (p: prog) (found : string list) : string list * string list =
    match p with
    | [] -> [], found
    | (Using s, meta)::t -> let name = String.split_on_char '.' 
        (List.hd (List.rev (String.split_on_char '/' s))) in
        if List.length name != 2 then
            error_meta meta ("Imported filenames must only have one extension")
        else 
        let filename = List.hd name in
        let extension = List.hd (List.tl name) in
        if not (extension = "lgl") then
            error_meta meta ("Extension " ^ extension ^ " not supported")
        else if List.mem filename found then
            error_meta meta ("Duplicate filename " ^ filename ^ " in import chain")
        else
            let tr,found' = search_prog t (filename::found) in
            s::tr, found'
    | _::t -> search_prog t found
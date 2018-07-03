(* A representation for a general context *)
(* A context is simply a finite map from 'a to 'b  *)
(* This implementation uses association lists. *)
type ('a, 'b) context = ('a * 'b) list

(* Make a new empty context. *)
let empty = []

(* Left-biased merge of two contexts *)
let merge c1 c2 = c1 @ c2

(* Look up a variable by name and return the associated letue. *)
(* Raises Not_found if no binding *)
let lookup c x = try List.assoc x c with | Not_found -> failwith "Undeclared variable"

(* Rebind var to value in context. *)
let update c x v = if List.mem_assoc x c then failwith "Duplicate" else (x, v) :: c

(* Produce bindings as an association list. *)
let bindings c = c

(* Check var exists in context *)
let mem c x = List.mem_assoc x c


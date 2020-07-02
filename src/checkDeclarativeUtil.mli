open Assoc
open Util
open GatorAst
open GatorAstPrinter
open CheckContexts
open CheckUtil

(** Uses aexp to bind all information to a declarative variable in a context *)
val bind_stip : contexts -> string -> aexp -> contexts

(** Check if variable is valid for use. Apply on all variable usage. *)
val is_valid : contexts -> string -> unit

(** Marks aexp as valid if its dependencies are valid *)
val validate_var : contexts -> aexp -> contexts * aexp

(** Invalidates all aexp in a list *)
val invalidate_arr : contexts -> aexp list -> contexts

(** Invalidates variable and its clients. Returns validated context and assignment expression *)
val invalidate_var : contexts -> aexp -> contexts

(** Bind a variable (aexp) as a client to another variable (string) *)
val bind_clients : contexts -> aexp -> string -> contexts

(** Ors the valid bits of two contexts *)
val intersect_valids : contexts -> contexts -> contexts

(** Ors the valid bits of before_if branche, if branch, else_if branch, and else branch contexts all in that order *)
val intersect_valids_if : contexts -> contexts -> contexts list -> contexts -> contexts
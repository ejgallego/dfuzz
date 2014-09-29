(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
open Syntax

(* Contexts of type 'a *)
type 'a ctx = (var_info * 'a) list

type context =
    {
      var_ctx   : ty ctx;
      tyvar_ctx : kind ctx;
      cs_ctx    : si_cs list;
    }

val empty_context : context

val extend_var   : string -> ty -> context -> context
val extend_ty_var : string -> kind -> context -> context
val extend_cs : si_cs -> context -> context

val remove_first_var   : context -> context
val remove_first_ty_var : context -> context

val access_var    : context -> int -> var_info * ty
val access_ty_var : context -> int -> var_info * kind

(* Name based functions for the parser *)
val lookup_var   : string -> context -> (var_info * ty) option
val lookup_tyvar : string -> context -> (var_info * kind) option

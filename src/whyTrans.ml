(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   Copyright (c) 2013, The IMDEA Software Institute
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

module WEnv = Why3.Env
module WT   = Why3.Theory
module WP   = Why3.Pretty

module WC   = WhyCore

module I  = Why3.Ident
module T  = Why3.Term
module Ty = Why3.Ty

module S  = Syntax
module P  = Print
module CS = Constr

open S
open CS

module H  = Hashtbl

open Support.Error
module Opts = Support.Options

(* Native @@ is already in ocaml 4.0 *)
let (@@) x y = x y

let dp = Support.FileInfo.dummyinfo

(* let dummy_e = L.mk_loc L._dummy @@ EConst ECUnit *)

let why_error   fi   = error_msg Opts.SMT fi

let why_warning fi   = message 1 Opts.SMT fi
let why_info    fi   = message 2 Opts.SMT fi
let why_info2   fi   = message 3 Opts.SMT fi
let why_debug   fi   = message 4 Opts.SMT fi
let why_debug2  fi   = message 5 Opts.SMT fi
let why_debug3  fi   = message 6 Opts.SMT fi

(* let unit_theory : WT.theory = WT.unit_theory *)
(* let list_theory : WT.theory = WEnv.find_theory WC.env ["list"] "List" *)
(* let exp_theory  : WT.theory = WEnv.find_theory WC.env ["real"] "ExpLog" *)
(* let fin_theory  : WT.theory = WEnv.find_theory WC.env ["real"] "FromInt" *)

let real_theory    : WT.theory = WEnv.read_theory WC.env ["real"] "Real"
let int_theory     : WT.theory = WEnv.read_theory WC.env ["int"]  "Int"
let dfuzz_theory   : WT.theory = WEnv.read_theory WC.env ["dFuzz"] "AbsR"

(* let dfuzz_r_theory : WT.theory = WEnv.find_theory WC.env ["dFuzz"]   "RealPosInf" *)
(* let dfuzz_i_theory : WT.theory = WEnv.find_theory WC.env ["dFuzz"]   "IntPos" *)

(* Type symbols *)
(* let ts_list = WT.ns_find_ts list_theory.WT.th_export ["list"] *)
(* let ts_unit = WT.ns_find_ts unit_theory.WT.th_export ["unit"] *)

(* let ts_rinf = WT.ns_find_ts dfuzz_r_theory.WT.th_export ["t"] *)

(* Get the why3 type of a kind *)
let why3_type kind = match kind with
  | Size -> Ty.ty_int
  (* | Sens -> Ty.ty_app ts_rinf [] *)
  | Sens -> Ty.ty_real
  | Star -> why_error dp "Type in numeric formula?"

let get_why3_sym th name =
  try WT.ns_find_ls th.WT.th_export [name]
  with Not_found -> why_error dp "Primitive %s cannot be mapped to Why3" name

(* Regular theory *)
(* let why3_eq = 
  WT.ns_find_ls real_theory.WT.th_export ["infix ="]

let why3_leq =
  WT.ns_find_ls real_theory.WT.th_export ["infix <="]

let why3_radd  = get_why3_sym real_theory "infix +"
let why3_rmult = get_why3_sym real_theory "infix *"

let why3_iadd  = get_why3_sym int_theory "infix +"
let why3_imult = get_why3_sym int_theory "infix *"

let why3_fromint = get_why3_sym fin_theory "from_int"
  *)

(* With infty
let why3_eq =
  WT.ns_find_ls dfuzz_r_theory.WT.th_export ["eq"]

let why3_leq =
  WT.ns_find_ls dfuzz_r_theory.WT.th_export ["le"]

let why3_radd  = get_why3_sym dfuzz_r_theory "add"
let why3_rmult = get_why3_sym dfuzz_r_theory "mul"

let why3_fromint  = get_why3_sym dfuzz_r_theory "fromInt"
let why3_fromreal = get_why3_sym dfuzz_r_theory "fromReal"
let why3_fromt    = get_why3_sym dfuzz_r_theory "fromT"

*)

let why3_eq =  WT.ns_find_ls real_theory.WT.th_export ["infix ="]
let why3_leq = WT.ns_find_ls real_theory.WT.th_export ["infix <="]

let why3_radd  = get_why3_sym real_theory "infix +"
let why3_rmult = get_why3_sym real_theory "infix *"

let why3_fromint  = get_why3_sym dfuzz_theory "fromInt"
let why3_fromreal = get_why3_sym dfuzz_theory "fromReal"

(* We need to keep track of the deBruijn Why3 variable mapping *)
let vmap : ((int, T.vsymbol) H.t) ref = ref (H.create 256)

let rec get_why3_var ctx v =
  let n     = v.v_name   in
  let index = v.v_index  in

  if H.mem !vmap index then
    H.find !vmap index
  else
    let (_bi, b_ty) = List.nth ctx v.v_index       in
    let v_ty        = why3_type b_ty               in
    why_debug3 dp "Getting type for %a : %a is %a" P.pp_vinfo v P.pp_kind b_ty WP.print_ty v_ty;

    let vt = T.create_vsymbol (I.id_fresh n) v_ty  in
    H.add !vmap index vt;
    (* Ugly but effective *)
    get_why3_var ctx v

let why3_int s   = T.t_const (Why3.Number.ConstInt (Why3.Number.int_const_of_int s))
let why3_float f =
  let (f,i) = modf f                                   in
  let is    = Printf.sprintf "%.0f" i                  in
  let fs    = String.sub (Printf.sprintf "%.3f" f) 2 3 in
  (* T.t_const (Why3.Number.ConstReal (Why3.Number.real_const_dec is fs None)) *)
  T.t_const Why3.Number.(ConstReal { rc_negative = false; rc_abs = real_const_dec is fs None}) Ty.ty_real

let why3_fin f =
  T.t_app_infer why3_fromreal [why3_float f]

(* Map si to why3 expressions *)
let rec why3_si ctx si =
  match si with
  | SiZero    -> why3_fin 0.0
  | SiSucc si -> let w_si = why3_si ctx si in
                 T.t_app_infer why3_radd [why3_fin 1.0; w_si]
  (* Reals *)
  (* | SiInfty *)
  | SiConst f -> why3_fin f
  | SiVar   v ->
    let w_v = T.t_var @@ get_why3_var ctx v in

    (* Cast to real if an int variable *)
    let (_, b_ty) = List.nth ctx v.v_index  in
    if b_ty = Size then
      T.t_app_infer why3_fromint [w_v]
    else
      T.t_app_infer why3_fromreal [w_v]

  | SiAdd (si1, si2) ->
    let w_si1 = why3_si ctx si1 in
    let w_si2 = why3_si ctx si2 in
    T.t_app_infer why3_radd [w_si1; w_si2]

  | SiMult (si1, si2) ->
    let w_si1 = why3_si ctx si1 in
    let w_si2 = why3_si ctx si2 in
    T.t_app_infer why3_rmult [w_si1; w_si2]
  | _ ->  why_error dp "Cannot translate extended sensitivities @[%a@]" P.pp_si si

let why3_eq_cs ctx (SiEq (si1, si2)) =
    let w_si1 = why3_si ctx si1 in
    let w_si2 = why3_si ctx si2 in
    T.ps_app why3_eq [w_si1; w_si2]

let why3_cs cs =
  let ctx     = cs.c_kind_ctx          in
  let w_lower = why3_si ctx cs.c_lower in
  let w_upper = why3_si ctx cs.c_upper in
  let leq     = T.ps_app why3_leq [w_lower; w_upper] in
  match cs.c_cs with
  | []        -> leq
  | (x :: xs) ->
    let prem = List.fold_left (fun eq re ->
      T.t_binary T.Tand (why3_eq_cs ctx re) eq)
      (why3_eq_cs ctx x) xs in
    T.t_binary T.Timplies prem leq


let close_term t =
  let fvm  = T.t_freevars T.Mvs.empty t                in
  let fvbl = T.Mvs.bindings fvm                        in
  let fvl  = List.map (fun (k, _) -> k) fvbl           in
  (* let vl   = List.concat (List.map serialize_vars fvl) in *)
  T.t_forall_close fvl [] t

let why3_translate cs =
  H.clear !vmap;

  let i = cs.c_info in

  try
    why_debug i "!*! Constraint to translate: @[%a@]" Print.pp_cs cs;

    let why3_term = why3_cs cs in

    why_debug i "Why3 ass: @[%a@]" WP.print_term why3_term;

    let why3_closed = close_term why3_term in
    why_debug i "Why3 closed: @[%a@]" WP.print_term why3_term;

    why3_closed

  with Ty.TypeMismatch(ty1, ty2) ->
    why_error i "Why3 type mismatch: @[%a@] vs @[%a@]" WP.print_ty ty1 WP.print_ty ty2

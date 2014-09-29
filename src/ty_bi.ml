(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
open Ctx
open Syntax
open Constr

open Support.Error
open Support.FileInfo

module Opt = Support.Options
module P   = Print

(* Type checking and synthesis engine for Fuzz.

*)

(* Errors *)
type ty_error_elem =
| SensError    of si * si
| MoreGeneral  of ty * ty
| TypeMismatch of ty * ty
| TypeInst     of ty * ty
| CannotApply  of ty * ty
| OccursCheck  of var_info * ty
| WrongShape   of ty * string
| WrongKind    of kind * kind
| NotSubtype   of ty * ty
| Internal     of string

let ty_seq = ref 0

let typing_error fi = error_msg    Opt.TypeChecker fi
let typing_error_pp = error_msg_pp Opt.TypeChecker

let ty_warning fi = message 1 Opt.TypeChecker fi
let ty_info    fi = message 2 Opt.TypeChecker fi
let ty_info2   fi = message 3 Opt.TypeChecker fi
let ty_debug   fi = message 4 Opt.TypeChecker fi
let ty_debug2  fi = message 5 Opt.TypeChecker fi
let ty_debug3  fi = message 6 Opt.TypeChecker fi

type 'a ty_error =
  Right of 'a
| Left  of ty_error_elem withinfo

(* Native @@ is already in ocaml 4.0 *)
let (@@) x y = x y

(* Reader/Error monad for type-checking *)
type 'a checker = context -> 'a ty_error

let (>>=) (m : 'a checker) (f : 'a -> 'b checker) : 'b checker =
  fun ctx ->
    match m ctx with
    | Right res -> f res ctx
    | Left e    -> Left e

let (>>) m f = m >>= fun _ -> f

let return (x : 'a) : 'a checker = fun ctx -> Right x

let get_ctx : context checker =
  fun ctx -> Right ctx

let get_ctx_length : int checker =
  get_ctx                             >>= fun ctx ->
  return @@ List.length ctx.var_ctx

let get_ty_ctx_length : int checker =
  get_ctx                             >>= fun ctx ->
  return @@ List.length ctx.tyvar_ctx

let with_new_ctx (f : context -> context) (m : 'a checker) : 'a checker =
  fun ctx -> m (f ctx)

let fail (i : info) (e : ty_error_elem) : 'a checker = fun _ ->
  Left { i = i; v = e }

let check_sens_leq i (sil : si) (sir : si) : unit checker =
  get_ctx >>= fun ctx ->
  if post_si_leq i ctx sil sir then
    return ()
  else
    fail i @@ SensError(sil, sir)

let check_sens_eq  i (sil : si) (sir : si) : unit checker =
  get_ctx >>= fun ctx ->
  if post_si_eq i ctx sil sir then
    return ()
  else
    fail i @@ SensError(sil, sir)

(* Constants *)
let si_zero  = SiConst 0.0
let si_one   = SiConst 1.0
let si_infty = SiInfty

(* Type of sensitivities augmented with □, with corresponding
   functions. In the type-checking algorithm, □ represents a binding
   that doesn't have an assigned sensitivity, which must be
   later on. *)
type bsi = si option

(* A list only with zero sensitivities *)
let zeros (n : int) : bsi list =
  let rec aux n l =
    if n = 0 then l else aux (n - 1) (None :: l) in
  aux n []

(* A list with zero sensitivities, except for one variable *)

(* Note that this has to be kept in sync with the actual ctx *)
let singleton (n : int) (v : var_info) : bsi list =
  let rec aux n l =
    if n = 0 then l
    else let si = if n = v.v_index + 1 then Some si_one else None in
         aux (n - 1) (si :: l) in
  aux n []

(* Extension of operations on regular sensitivities to augmented
   sensitivities *)

let add_bsi (bsi1 : bsi) (bsi2 : bsi) : bsi =
  match bsi1, bsi2 with
  | Some si1, Some si2 -> Some (SiAdd (si1, si2))
  | Some si, None
  | None, Some si -> Some si
  | None, None -> None

let mult_bsi (bsi1 : bsi) (bsi2 : bsi) : bsi =
  match bsi1, bsi2 with
  | Some si1, Some si2 -> Some (SiMult (si1, si2))
  | _, _ -> None

let si_of_bsi (bsi : bsi) : si =
  Option.default si_zero bsi

let lub_bsi (bsi1 : bsi) (bsi2 : bsi) : bsi =
  match bsi1, bsi2 with
  | Some si1, Some si2 -> Some (SiLub (si1, si2))
  | Some si, None
  | None, Some si -> Some si
  | None, None -> None

let sup_bsi (bi : binder_info) (k : kind) (bsi : bsi) : bsi =
  Option.map (fun si -> SiSup (bi, k, si)) bsi

(* NB: The scrutinee is always a regular sensitivity (i.e. not box),
   because it always comes from the index of a type, which *)
let case_bsi (si : si) (bsi0 : bsi) (bi : binder_info) (bsin : bsi) : bsi =
  match bsi0, bsin with
  | None, None -> None
  | _, _ -> Some (SiCase (si, si_of_bsi bsi0, bi, si_of_bsi bsin))

let cs_add_eq (sil : si) (sir : si) =
  extend_cs (SiEq (sil, sir))

module TypeSub = struct

  let check_prim_sub (i : info) (ty_f : ty_prim) (ty_a : ty_prim) : unit checker =
    match ty_f, ty_a with
    | PrimNum, PrimClipped -> return ()
    | _   when ty_f = ty_a -> return ()
    | _                    -> fail i @@ NotSubtype (TyPrim ty_f, TyPrim ty_a)

  (* Check whether ty_1 is a subtype of ty_2, generating the necessary
     constraints along the way. *)
  let rec check_type_sub (i : info) (ty_1 : ty) (ty_2 : ty) : unit checker =
    let fail = fail i @@ NotSubtype (ty_1, ty_2) in
    match ty_1, ty_2 with
    | TyVar v1, TyVar v2   ->
      if v1 = v2 then return () else fail

    | TyPrim p1, TyPrim p2 -> check_prim_sub i p1 p2

    | TyPrim1(pl, tyl), TyPrim1(pr, tyr) ->
      if pl = pr then check_type_sub i tyl tyr else fail

    | TyUnion(tyl1, tyl2), TyUnion(tyr1, tyr2) ->
      check_type_sub i tyl1 tyr1 >>
      check_type_sub i tyl2 tyr2

    | TyTensor(tyl1, tyl2), TyTensor(tyr1, tyr2) ->
      check_type_sub i tyl1 tyr1 >>
      check_type_sub i tyl2 tyr2

    | TyAmpersand(tyl1, tyl2), TyAmpersand(tyr1, tyr2) ->
      check_type_sub i tyl1 tyr1 >>
      check_type_sub i tyl2 tyr2

    | TyLollipop(tyl1, sil, tyl2), TyLollipop(tyr1, sir, tyr2) ->
      check_type_sub i tyr1 tyl1 >>
      check_type_sub i tyl2 tyr2 >>
      check_sens_leq i sir sil

    | TyMu(_bl, tyl), TyMu(_br, tyr) ->
      (* Recursive types disabled for now *)
      fail

    | TyForall(bl, kl, tyl), TyForall(_br, kr, tyr) ->
      if kl = kr then
        with_new_ctx (extend_ty_var bl.b_name kl) begin
          check_type_sub i tyl tyr
        end
      else fail

    | TySizedNat(sil), TySizedNat(sir) ->
      check_sens_eq i sil sir

    | TySizedNum(sil), TySizedNum(sir) ->
      check_sens_eq i sil sir

    (* Subtype both sized types to standard reals if needed. *)
    | TySizedNat(sil), TyPrim PrimInt ->
      return ()

    | TySizedNum(sil), TyPrim PrimNum ->
      return ()

    | TyList(tyl, sil), TyList(tyr, sir) ->
      check_type_sub i tyl tyr >>
      check_sens_eq  i sil sir

    | _, _ -> fail

  (* Check whether ty is compatible (modulo subtyping) with annotation
     ann, returning the resulting type. *)
  let check_type_ann (i : info) (ann : ty option) (ty : ty) : ty checker =
    match ann with
    | Some ty' -> check_type_sub i ty ty' >> return ty'
    | None -> return ty

  (* Checks for types of different shapes *)

  (* Check that the type is an application and can be applied to
     arg. Return the result and sensitivity of the application *)
  let check_ty_app_shape i ty_arr =
    match ty_arr with
    | TyForall(_b, k, ty) -> return (ty, k)
    | _                   -> fail i @@ CannotApply(ty_arr, ty_arr)

  (* This is good for return, eq, etc... it should be extended
     systematically instead of the current hack *)
  let infer_tyapp_very_simple i ty ty_arg =
    match ty with
    | TyLollipop(TyVar v, si, tyb) ->
      if v.v_index = 0 then
        let nt = ty_subst 0 ty_arg tyb in
        ty_debug i "==> [%3d] Inferring type application from @[%a@] to @[%a@]" !ty_seq Print.pp_type tyb Print.pp_type nt;
        return (nt, si)
      else
        fail i @@ CannotApply(ty, ty_arg)
    | TyLollipop(TyPrim1 (t, TyVar v), si, tyb) ->
      begin match ty_arg with
      | TyPrim1 (t1, ty_arg') ->
        if v.v_index = 0 && t1 = t then
          let nt = ty_subst 0 ty_arg' tyb in
          ty_debug i "==> [%3d] Inferring container type application from @[%a@] to @[%a@]" !ty_seq Print.pp_type tyb Print.pp_type nt;
          return (nt, si)
        else
          fail i @@ CannotApply(ty, ty_arg)
      | _ -> fail i @@ CannotApply(ty, ty_arg)
      end
    | _ -> fail i @@ CannotApply(ty, ty_arg)

  let check_app i ty_arr ty_arg =
    ty_debug i "<-> [%3d] Application of @[%a@] to @[%a@]" !ty_seq Print.pp_type ty_arr Print.pp_type ty_arg;
    match ty_arr with
    (* Here we do inference of type applications *)
    | TyForall(bi, Star, ty)   ->
      infer_tyapp_very_simple i ty ty_arg

    | TyLollipop(tya, si, tyb) ->
      check_type_sub i tya ty_arg >>
      return (tyb, si)
    | _                        -> fail i @@ CannotApply(ty_arr, ty_arg)

  let check_fuzz_shape i ty =
    match ty with
    | TyPrim1 (Prim1Fuzzy, ty) -> return ty
    | _                        -> fail i @@ WrongShape (ty, "fuzzy")

  let check_tensor_shape i ty =
    match ty with
    | TyTensor(ty1, ty2) -> return (ty1, ty2)
    | _                  -> fail i @@ WrongShape (ty, "tensor")

  let check_union_shape i ty =
    match ty with
    | TyUnion(ty1, ty2) -> return (ty1, ty2)
    | _                 -> fail i @@ WrongShape (ty, "union")

  let check_sized_nat_shape i ty =
    match ty with
    | TySizedNat si -> return si
    | _             -> fail i @@ WrongShape (ty, "nat")

  let check_list_shape i ty =
    match ty with
    | TyList (ty, si) -> return (ty, si)
    | _               -> fail i @@ WrongShape (ty, "list")

  let check_mu_shape i ty =
    match ty with
    | TyMu(_, _)          -> typing_error i "Iso-recursive types disabled for now"
    | _                   -> fail i @@ WrongShape (ty, "mu")

end

open TypeSub

(* Extend the context with a type binding and run a computation *)
let with_extended_ty_ctx (v : string) (k : kind) (m : 'a checker) : 'a checker =
  with_new_ctx (extend_ty_var v k) m

(* Extend the context with a value binding and run a computation. The
   computation is assumed to produce a list of results, one for each
   variable in the extended context. That list is destructed, and the
   result corresponding to the new variable is returned separately for
   convenience. *)
let with_extended_ctx (i : info) (v : string) (ty : ty) (m : ('a * 'b list) checker) :
    ('a * 'b * 'b list) checker =
  with_new_ctx (extend_var v ty) m >>= fun (res, res_ext_ctx) ->
  match res_ext_ctx with
  | res_v :: res_ctx -> return (res, res_v, res_ctx)
  | [] -> fail i @@ Internal "Computation on extended context didn't produce enough results"

(* Similar to the one above, but with two variables. vx has index 1 in
   the extended context, while vy has index 0. The order of the
   returned results matches those of the arguments. *)
let with_extended_ctx_2 (i : info)
    (vx : string) (tyx : ty) (vy : string) (tyy : ty)
    (m : ('a * 'b list) checker) : ('a * 'b * 'b * 'b list) checker =
  with_new_ctx (fun ctx -> extend_var vy tyy (extend_var vx tyx ctx)) m >>= fun (res, res_ext_ctx) ->
  match res_ext_ctx with
  | res_y :: res_x :: res_ctx -> return (res, res_x, res_y, res_ctx)
  | _ -> fail i @@ Internal "Computation on extended context didn't produce enough results"

let get_var_ty (v : var_info) : ty checker =
  get_ctx >>= fun ctx ->
  return @@ snd (access_var ctx v.v_index)

let add_sens (bsis1 : bsi list) (bsis2 : bsi list) : bsi list =
  List.map2 add_bsi bsis1 bsis2

let scale_sens (bsi : bsi) (bsis : bsi list) : bsi list =
  List.map (mult_bsi bsi) bsis

let lub_sens (bsis1 : bsi list) (bsis2 : bsi list) : bsi list =
  List.map2 lub_bsi bsis1 bsis2

let sup_sens (bi : binder_info) (k : kind) (bsis : bsi list) : bsi list =
  List.map (sup_bsi bi k) bsis

let case_sens (si : si) (bsis0 : bsi list) (bi : binder_info) (bsisn : bsi list) : bsi list =
  List.map2 (fun bsi0 bsin -> case_bsi si bsi0 bi bsin) bsis0 bsisn

(**********************************************************************)
(* Main typing routines                                               *)
(**********************************************************************)
let rec kind_of (i : info) (si : si) : kind checker =
  ty_debug i "--> [%3d] Enter kind_of: @[%10a@]" !ty_seq
    (Print.limit_boxes Print.pp_si) si; incr ty_seq;

  let ck k = if k <> Star then return k else fail i @@ WrongKind(Sens, k) in

  (match si with
  | SiZero        -> return Size
  | SiInfty       -> return Sens
  | SiConst _     -> return Sens
  | SiSucc  s     ->
    kind_of i s      >>= fun k ->
    if k = Size
    then return k
    else fail i @@ WrongKind(Size, k)

  | SiVar   v     ->
    get_ctx >>= fun ctx ->
    ck @@ snd @@ access_ty_var ctx v.v_index

  | SiAdd  (x, y)
  | SiMult (x, y)
  | SiLub  (x, y) ->
    kind_of i x >>= ck >>
    kind_of i y >>= ck >>
    return Sens

  | SiSup  (bi, k, s)         ->
    with_extended_ty_ctx bi.b_name k (kind_of i s) >>= fun k' ->
    if k <> Star then return Sens else fail i @@ WrongKind(Sens,k)

  | SiCase (s, s0, bi, sn) ->
    kind_of i s >>= fun k ->
    if k <> Size
    then fail i @@ WrongKind(Size,k)
    else kind_of i s0                                       >>= ck >>
         with_extended_ty_ctx bi.b_name Size (kind_of i sn) >>= ck >>
         return Sens

  ) >>= fun k ->

  decr ty_seq;
  (* We limit pp_term *)
  ty_debug i "<-- [%3d] Exit kind_of: @[%a@] with kind @[%a@]" !ty_seq
    (Print.limit_boxes Print.pp_si) si Print.pp_kind k;
  return k

(* Given a term t and a context ctx for that term, check whether t is
   typeable under ctx, returning a type for t, a list of synthesized
   sensitivities for ctx, and a list of constraints that need to be
   satisfied in order for the type to be valid. Raises an error if it
   detects that no typing is possible. *)

let rec type_of (t : term) : (ty * bsi list) checker  =

  ty_debug (tmInfo t) "--> [%3d] Enter type_of: @[%10a@]" !ty_seq
    (Print.limit_boxes Print.pp_term) t; incr ty_seq;

  (match t with
  (* Variables *)
  | TmVar(i, v)  ->
    get_ctx_length              >>= fun len ->
    get_var_ty v                >>= fun ty  ->
    return (ty, singleton len v)

  (* Primitive terms *)
  | TmPrim(_, pt) ->
    get_ctx_length >>= fun len ->
    return (type_of_prim pt, zeros len)

  (* Abstraction and Application *)

  (* λ (x :[si] tya_x) : tya_tm { tm } *)
  | TmAbs(i, b_x, (sia_x, tya_x), otya_tm, tm) ->

    with_extended_ctx i b_x.b_name tya_x (type_of tm) >>= fun (ty_tm, si_x, sis) ->

    ty_debug (tmInfo t) "### [%3d] Inferred sensitivity for binder @[%a@] is @[%a@]" !ty_seq P.pp_binfo b_x P.pp_si (si_of_bsi si_x);

    check_type_ann i otya_tm ty_tm                    >>
      check_sens_leq i (si_of_bsi si_x) sia_x         >>
      return (TyLollipop (tya_x, sia_x, ty_tm), sis)

  (* tm1 !ᵢβ → α, tm2: β *)
  | TmApp(i, tm1, tm2)                             ->

    type_of tm1 >>= fun (ty1, sis1) ->
    type_of tm2 >>= fun (ty2, sis2) ->

    (* Checks that ty1 has shape !ᵢβ → α, and that ty2 is and instance of β.
       Returns α and the sensitivity inside ty1 *)
    check_app i ty1 ty2 >>= fun (tya, r) ->

    (* We scale by the sensitivity in the type, which comes from an annotation *)
    return (tya, add_sens sis1 (scale_sens (Some r) sis2))

  (************************************************************)
  (* Identical to app + lam, this rule exists in order to avoid too
     many type annotations!
  *)

  (* let x [: otya_x] = tm in e *)
  | TmLet(i, x, sia_x, tm_x, e)                   ->

    type_of tm_x >>= fun (ty_x, sis_x)  ->

    ty_info2 i "### Type of binder %a is %a" Print.pp_binfo x Print.pp_type ty_x;

    with_extended_ctx i x.b_name ty_x (type_of e) >>= fun (ty_e, si_x, sis_e) ->
    check_sens_leq i (si_of_bsi si_x) sia_x                 >>
      return (ty_e, add_sens sis_e (scale_sens si_x sis_x))

  | TmLetRec(i, x, tya_x, tm_x, e)                      ->

    with_extended_ctx i x.b_name tya_x (type_of tm_x) >>= fun (ty_x, si_x, sis_x) ->

    (* XXX: Double check: before, this used to be backwards. *)
    (* JH: LGTM *)
    check_type_sub i ty_x tya_x >>

    (* AAA: What happened here before seemed strange. We fed x into
       e's context and assigned it a sensitivity of ∞. It seems that
       this shouldn't be necessary, given that we are multiplying the
       context by ∞ anyway... *)
      with_extended_ctx i x.b_name tya_x (type_of e) >>= fun (ty_e, si_x', sis_e) ->

    ty_info2 i "### Type of binder %a is %a" Print.pp_binfo x Print.pp_type ty_x;
    return (ty_e, add_sens sis_e (scale_sens (mult_bsi (Some si_infty) si_x') sis_x))

  | TmSample(i, b_x, tm_x, e)                              ->

    type_of tm_x            >>= fun (ty_x, sis_x) ->
    check_fuzz_shape i ty_x >>= fun ty_x ->

    with_extended_ctx i b_x.b_name ty_x (type_of e) >>= fun (ty_e, si_x, sis_e) ->

    ty_debug (tmInfo t) "### [%3d] Sample for binder @[%a@] with sens @[%a@]" !ty_seq P.pp_binfo b_x P.pp_si (si_of_bsi si_x);

    check_fuzz_shape i ty_e                         >>

    (* The inferred sensitivity of x can be ignored. Once the result
       of a differentially private computation has been published, it
       can be used without any restriction. *)
    return (ty_e, add_sens sis_x sis_e)

  (* Tensor and & *)
  | TmAmpersand(i, tm1, tm2)      ->

    type_of tm1 >>= fun (ty1, sis1) ->
    type_of tm2 >>= fun (ty2, sis2) ->

    return (TyAmpersand(ty1, ty2), lub_sens sis1 sis2)

  (************************************************************)
  (* Data type manipulation *)
  | TmFold(i, ty, tm)               ->
    fail i @@ Internal "Not implemented: fold"

  | TmUnfold (i, tm)                ->
    fail i @@ Internal "Not implemented: unfold"

  (* Aliases *)
  | TmTypedef(i, n, tdef_ty, tm)    ->

    ty_debug3 i "Calling typedef %a = %a on term %a" Print.pp_binfo n Print.pp_type tdef_ty Print.pp_term tm;

    (* We just substitute the type for the variable. *)
    let tm'         = term_ty_subst 0 tdef_ty tm   in
    type_of tm'

  | TmPair(i, e1, e2) ->

    type_of e1 >>= fun (ty1, sis1) ->
    type_of e2 >>= fun (ty2, sis2) ->

    return @@ (TyTensor(ty1, ty2), add_sens sis1 sis2)

  (* let (x,y) = e in e' *)
  | TmTensDest(i, x, y, e, t) ->

    type_of e >>= fun (ty_e, sis_e) ->
    check_tensor_shape i ty_e >>= fun (ty_x, ty_y) ->

    (* Extend context with x and y *)
    with_extended_ctx_2 i x.b_name ty_x y.b_name ty_y (type_of t) >>= fun (ty_t, si_x, si_y, sis_t) ->

    let si_x = si_of_bsi si_x in
    let si_y = si_of_bsi si_y in

    return (ty_t, add_sens sis_t (scale_sens (Some (SiLub (si_x, si_y))) sis_e))

  (* case e of inl(x) => e_l | inr(y) e_r *)
  (* FIXME: Do we still need the sensitivity annotation on e? It's
     being ignored right now. *)
  (* JH: The paper has it in. We thought maybe we could remove the annotation,
   * but it's not clear to me. Is it even being parsed yet? *)
  (* AAA: Which paper? The case statement for nats in our ICFP
     submission (which is the closest thing we have to sums there)
     doesn't have any annotations, and the algorithm doesn't rely on
     them. The parser *seems* to be reading some sensitivity
     annotation for UNIONCASE. *)
  (* FIXME: Since the paper doesn't formalize sums, I tried to guess
     what the correct rule here would be. We should double-check this. *)
  (* EG: Do we need a type anotation here? *)
  (* AAA: I think so. We'll infer two types, one for each branch. We
     could check that both are equal (i.e., t1 <= t2 and t2 <= t1),
     but the resultning typing rule would be too restrictive, no? *)

  | TmUnionCase(i, e, sia_e, ty, b_x, e_l, b_y, e_r)      ->

    type_of e >>= fun (ty_e, sis_e) ->

    check_union_shape i ty_e >>= fun (ty1, ty2) ->

    with_extended_ctx i b_x.b_name ty1 (type_of e_l) >>= fun (tyl, si_x, sis_l) ->
    check_type_sub i tyl ty >>

      with_extended_ctx i b_y.b_name ty2 (type_of e_r) >>= fun (tyr, si_y, sis_r) ->
    check_type_sub i tyr ty >>

      let si_x = si_of_bsi si_x in
      let si_y = si_of_bsi si_y in

      return (ty, add_sens (lub_sens sis_l sis_r) (scale_sens (Some (SiLub (si_x, si_y))) sis_e))

  (* Type/Sensitivity Abstraction and Application *)
  | TmTyAbs(i, bi, ki, tm) ->

    with_extended_ty_ctx bi.b_name ki (type_of tm) >>= fun (ty, sis) ->
    return (TyForall(bi, ki, ty), sup_sens bi ki sis)

  | TmTyApp(i, tm, ty_app) ->

    type_of tm                >>= fun (ty_t, sis) ->
    check_ty_app_shape i ty_t >>= fun (ty_i, k) ->

    if k = Star then
      return (ty_subst 0 ty_app ty_i, sis)
    else
      fail i @@ WrongKind(Star, k)

  | TmSiApp(i, tm, si_app)      ->

    type_of tm                >>= fun (ty_t, sis) ->
    check_ty_app_shape i ty_t >>= fun (ty_i, k) ->

    (* XXX: Check the application is well-typed wrt to the kind! *)
    if k <> Star then
      return (ty_si_subst 0 si_app ty_i, sis)
    else
      fail i @@ WrongKind(Sens, k)

  (* Dependent pattern matching *)
  | TmNatCase(i, e, ty, ztm, nat, si, stm) ->

    type_of e                    >>= fun (ty_e, sis_e) ->
    check_sized_nat_shape i ty_e >>= fun sz ->
    (* XXX: Do we need to check that sz has kind Size? *)
    (* EG: It wouldn't hurt, but I cannot see how it could slip. *)

    (* Case for Zero *)
    with_new_ctx (cs_add_eq sz SiZero) begin
      type_of ztm                >>= fun (ty_ztm, sis_ztm) ->
      check_type_sub i ty_ztm ty >>
      return (ty_ztm, sis_ztm)
    end                          >>= fun (ty_ztm, sis_ztm) ->

    (* Case for Succ n *)
    with_extended_ty_ctx si.b_name Size begin

      (* Get the newly introduced sens variable and create a term for it *)
      get_ctx                           >>= fun ctx ->
      let (vi, _) = access_ty_var ctx 0 in
      let sz'     = SiVar vi            in

      (* New variable of type Nat[n] *)
      with_extended_ctx i nat.b_name (TySizedNat sz') begin

        (* NOTE: sz must be shifted, it comes from a smaller context *)
        let sz_s = si_shift 0 1 sz in

        with_new_ctx (cs_add_eq sz_s (SiSucc sz')) begin
          type_of stm                     >>= fun (ty_stm, sis_stm) ->

          (* Note: ty must be shifted! *)
          let s_ty = ty_shift 0 1 ty      in
          check_type_sub i ty_stm s_ty    >>
          return (ty_stm, sis_stm)
        end
      end
    end >>= fun (_ty_stm, si_nat, sis_stm) ->

    (* XXX: Review this *)
    return (ty, add_sens (case_sens sz sis_ztm si sis_stm)
      (scale_sens (Some (SiCase (sz, si_zero, si, si_of_bsi si_nat)))
         sis_e))

  | TmListCase(i, tm, ty, ntm, elem, list, si, ctm) ->
    (* XXX: Again, this is based on natcase, but since this was not
       explicitly formalized in the paper, we should double-check this
       really carefully *)
    (* EG: LGTM *)

    type_of tm              >>= fun (ty_e, sis_e) ->
    check_list_shape i ty_e >>= fun (ty_e', sz) ->
    (* XXX: Do we need to check that sz has kind Size? *)
    (* EG: It wouldn't hurt, but I cannot see how it could slip. *)

    (* Case for nil, ntm *)
    with_new_ctx (cs_add_eq sz SiZero) begin
      type_of ntm                >>= fun (ty_ntm, sis_ntm) ->
      check_type_sub i ty_ntm ty >>
      return (ty_ntm, sis_ntm)
    end >>= fun (ty_ntm, sis_ntm) ->

    (* Case for cons *)
    with_extended_ty_ctx si.b_name Size begin

      (* Get the newly introduced sens variable and create a term for it *)
      get_ctx                           >>= fun ctx ->
      let (vi, _) = access_ty_var ctx 0 in
      let sz'     = SiVar vi            in

      (* We must shift the list types as we are under an extended context. *)
      let ty_e_s = ty_shift 0 1 ty_e' in
      with_extended_ctx_2 i elem.b_name ty_e_s list.b_name (TyList (ty_e_s, sz')) begin

        (* NOTE: sz must be shifted, it comes from a smaller context *)
        let sz_s = si_shift 0 1 sz in

        with_new_ctx (cs_add_eq sz_s (SiSucc sz')) begin
          type_of ctm                     >>= fun (ty_ctm, sis_ctm) ->

          (* Note: ty must be shifted! *)
          let ty_s = ty_shift 0 1 ty      in

          check_type_sub i ty_ctm ty_s    >>
          return (ty_ctm, sis_ctm)
        end
      end
    end >>= fun (_ty_rtm, si_elem, si_list, sis_ctm) ->

    let si_elem = si_of_bsi si_elem in
    let si_list = si_of_bsi si_list in

    (* XXX: Taking the lub on the succ branch by analogy with tensor
       elim; double-check *)
    (* JH: LGMT *)
    (* EG: Indeed Need to double-check *)
    return (ty, add_sens (case_sens sz sis_ntm si sis_ctm)
      (scale_sens (Some (SiCase (sz, si_zero, si, SiLub (si_elem, si_list))))
         sis_e))

  (* Pack/Unpack *)
  | TmPack(i, _, _, _)               ->
    typing_error i "DFuzz stub: Pack"

  | TmUnpack(i, _n, _si, _t1, _t2)   ->
    typing_error i "DFuzz stub: Unpack"

  ) >>= fun (ty, sis) ->

  decr ty_seq;
  (* We limit pp_term *)
  ty_debug (tmInfo t) "<-- [%3d] Exit type_of : @[%a@] with type @[%a@]" !ty_seq
    (Print.limit_boxes Print.pp_term) t Print.pp_type ty;

  (* TODO: pretty printer for sensitivities *)
  (* ty_debug2 (tmInfo t) "<-- Context: @[%a@]" Print.pp_context ctx; *)

  return (ty, sis)

open Format
open Print

let pp_tyerr ppf s = match s with
  | SensError (si1, si2)  -> fprintf ppf "EEE [%3d] Cannot satisfy constraint %a <= %a" !ty_seq pp_si si1 pp_si si2
  | MoreGeneral(ty1, ty2) -> fprintf ppf "EEE [%3d] %a is not more general than %a"     !ty_seq pp_type ty1 pp_type ty2
  | TypeInst(ty1, ty2)    -> fprintf ppf "EEE [%3d] Type %a is not instance of %a"      !ty_seq pp_type ty1 pp_type ty2
  | TypeMismatch(ty1, ty2)-> fprintf ppf "EEE [%3d] Cannot unify %a with %a"        !ty_seq pp_type ty1 pp_type ty2
  | CannotApply(ty1, ty2) -> fprintf ppf "EEE [%3d] Cannot apply %a to %a"    !ty_seq pp_type ty1 pp_type ty2
  | OccursCheck(v, ty)    -> fprintf ppf "EEE [%3d] Cannot build infinite type %a = %a" !ty_seq pp_vinfo v pp_type ty
  | WrongShape(ty, sh)    -> fprintf ppf "EEE [%3d] Type %a has wrong shape, expected %s type." !ty_seq pp_type ty sh
  | WrongKind(k1, k2)     -> fprintf ppf "EEE [%3d] Kind mismatch expected %a found %a." !ty_seq pp_kind k1 pp_kind k2
  | NotSubtype(ty1,ty2)   -> fprintf ppf "EEE [%3d] %a is not a subtype of %a" !ty_seq pp_type ty1 pp_type ty2
  | Internal s            -> fprintf ppf "EEE [%3d] Internal error: %s" !ty_seq s

(* Equivalent to run *)
let get_type program =
  match type_of program Ctx.empty_context with
  | Right (ty, _sis) -> ty
  | Left e ->
    typing_error_pp e.i pp_tyerr e.v

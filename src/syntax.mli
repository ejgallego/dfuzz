(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
open Support.FileInfo

(* Different types of variable binding, for debug purposes *)
type fuzz_binding =
    BiVar    (* Regular varible *)
  | BiTyVar  (* Type variable   *)
  | BiETyVar (* Existential variable  *)

(* Variables and binders *)
type var_info = {
  v_index : int;

  (* Debug fields *)
  v_name  : string;
  v_size  : int;
  v_type  : fuzz_binding;
}

(* Default var_info *)
val dvi : var_info

(* Adds n to a var_info *)
val var_shift : int -> int -> var_info -> var_info

(* All of the fields are debug information *)

type binder_info = {
  b_name : string;
  b_size : int;          (* How many outside binders we had when this binded was found *)
  b_type : fuzz_binding;
  b_prim : bool;
}

(* Types *)

(* Part 0: kinds *)
type kind =
    Star
  | Size
  | Sens

(* Part 1: Sensitivites *)
type si =
  (* Sizes *)
  | SiZero
  | SiSucc  of si
  (* Reals *)
  | SiInfty
  | SiConst of float
  | SiVar   of var_info
  | SiAdd   of si * si
  | SiMult  of si * si
  | SiLub   of si * si
  (* We only allow to sup the first variable *)
  | SiSup   of binder_info * kind * si
  | SiCase  of si * si * binder_info * si

(* Shift variable indexes by n *)
val si_shift : int -> int -> si -> si

type si_cs = SiEq of (si * si)

val cs_shift : int -> int -> si_cs -> si_cs

(* Number of binders, index, and sens *)
(* Part 2: Regular "HM" types *)
(* Primitive types *)
type ty_prim =
    PrimNum
  | PrimInt
  | PrimUnit
  | PrimBool
  | PrimString
  | PrimClipped
  | PrimDBS

(* Types with one argument *)
(* XXX: Extend to types with n-ary arguments *)
type ty_prim1 =
    Prim1Set
  | Prim1Bag
  | Prim1Fuzzy

type ty =
  (* variables used in bindings *)
    TyVar  of var_info

  (* Primitive types *)
  | TyPrim  of ty_prim
  | TyPrim1 of (ty_prim1 * ty)

  (* ADT *)
  | TyUnion     of ty * ty
  | TyTensor    of ty * ty
  | TyAmpersand of ty * ty

  (* Functional type *)
  | TyLollipop of ty * si * ty

  (* Fixpoint type *)
  | TyMu of binder_info * ty

  (* Quantified types *)
  | TyForall     of binder_info * kind * ty
  | TyExistsSize of binder_info * ty

  (********************************************************************)
  (* Dependent types *)
  | TySizedNat of si
  | TySizedNum of si
  | TyList     of ty * si

(* XXX: This is incorrect, right now it shifts all the indexes, thus
   it is buggy, see the other comment *)

(* Shift all the open indexes by n *)
val ty_shift : int -> int -> ty -> ty

(* Substitutions *)

(* Capture avoiding sub, the term must be dependent on the number of
   binders under it is replaced *)
val ty_subst     : int -> ty -> ty -> ty
val ty_si_subst  : int -> si -> ty -> ty

(* Terms *)

(* Primitive Terms *)
type term_prim =
    PrimTUnit
  | PrimTNum    of float
  | PrimTInt    of int
  | PrimTBool   of bool
  | PrimTString of string
  | PrimTFun    of string * ty
  | PrimTDBS    of string

val type_of_prim : term_prim -> ty

type term =
    TmVar of info * var_info

  (*  *)
  | TmPair      of info * term * term
  (* | TmTensDest  of info * binder_info * binder_info * si * term * term *)
  | TmTensDest  of info * binder_info * binder_info * term * term

  | TmUnionCase of info * term * si * ty           * binder_info * term * binder_info * term
  (*                      t      [si] return ty of { inl(x)     => tm1  | inl(y)     => tm2  } *)

  (* Primitive terms *)
  | TmPrim     of info * term_prim

  (* The three fundamental constructs of our language: *)

  (* Regular Abstraction and Applicacion *)
  | TmApp of info * term * term

  (* In a lambda is possible to independently annotate the input and return type *)
  | TmAbs of info * binder_info * (si * ty) * ty option * term

  (* & constructor *)
  | TmAmpersand of info * term * term

  (* Recursive data types *)
  | TmFold    of info * ty * term
  | TmUnfold  of info * term

  (* Only needed for polymorphism *)
  | TmLet      of info * binder_info * si * term * term
  | TmLetRec   of info * binder_info * ty * term * term
  | TmSample   of info * binder_info * term * term

  (***********************************************************************)
  (* What to do with this, what is the typing rule?                      *)
  | TmTypedef of info * binder_info * ty * term

  (***********************************************************************)
  (* Dependent case expressions, removal pending on type constraints     *)

  (*                      t      return ty of {nil => tm1  | (    x     ::     xs      ) [si]       => tm2 } *)
  | TmListCase  of info * term * ty                 * term * binder_info * binder_info * binder_info * term
  (*                      t      return ty of {Z   => tm1  | (S x)         [si]       => tm2 }                 *)
  | TmNatCase   of info * term * ty                 * term * binder_info * binder_info * term

  (* Pack/Unpack *)
  | TmPack of info * term * si * ty
  | TmUnpack of info * binder_info * binder_info * term * term

  (* Sensitity Abstraction and Applicacion *)
  | TmTyAbs of info * binder_info * kind * term
  | TmSiApp of info * term * si
  | TmTyApp of info * term * ty

val tmInfo : term -> info

(* Substitution for type and sens annotations *)
(* tm[t/x] *)
val term_ty_subst : int -> ty -> term -> term
val term_si_subst : int -> si -> term -> term

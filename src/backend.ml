(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
open Format

open Syntax

(*
  We compile to native Caml code
*)

let header =
"open Prim
open Bag
open Db_sources
open Init

let query =
"

let body =
"
let () = exit (fuzz_main query)"

let paren s = "(" ^ s ^ ")"

let gen_primitive prim =
  match prim with
    PrimTUnit        -> "()"
  | PrimTNum(r)      -> string_of_float r
  | PrimTInt(n)      -> string_of_int   n
  | PrimTBool(b)     -> string_of_bool  b
  | PrimTString(s)   -> "\"" ^ s ^ "\""
  | PrimTFun(f, _ty) -> f
  | PrimTDBS s       -> paren ("DBS \"" ^ s ^ "\"")

(* Avoid clashes with ML names *)
let ml_n n = "_" ^ n
let ml_b b = "_" ^ b.b_name

let rec gen_term ppf t =
  match t with
      (* TODO: not very happy using debug information for this, generate
         names from the index in the future *)
      TmVar (_, v)  ->
        begin
          match v.v_name with
          | "p_inl"      -> fprintf ppf "Left"
          | "p_inr"      -> fprintf ppf "Right"
          (* | "num2string" -> fprintf ppf "" *)
          | _           ->  fprintf ppf "%s" (ml_n v.v_name)
        end
    (* Will be represented as applications soon *)
    | TmPair (_,  e1, e2) ->
      fprintf ppf "(%a, %a)" gen_term e1 gen_term e2

    | TmTensDest (_,  b_x, b_y, tm_e1, tm_e2) ->
    (* | TmTensDest (_,  b_x, b_y, _si, tm_e1, tm_e2) -> *)
      fprintf ppf "(let (%s,%s) =  %a in@\n@[%a@])"
        (ml_b b_x) (ml_b b_y) gen_term tm_e1 gen_term tm_e2

    | TmUnionCase (_, tm_e, _ty, _si, bi_l, tm_l, bi_r, tm_r) ->
      fprintf ppf "(match %a with @[<v>| Left %s -> %a @,| Right %s -> %a@])"
        gen_term tm_e (ml_b bi_l) gen_term tm_l (ml_b bi_r) gen_term tm_r

    (* Regular stuff for fuzz *)
    | TmPrim (_, prim) -> fprintf ppf "%s" (gen_primitive prim)

    | TmApp (_, f, e)  ->
      (* Some (hacky) optimizations for the OCaml translation *)
      begin
        match f with
        (* Binary operations *)
        | TmApp (_, TmVar(_, v), e') ->
          begin
            match v.v_name with
            | "op_add"      -> fprintf ppf "(%a +. %a)" gen_term e' gen_term e
            | "op_sub"      -> fprintf ppf "(%a -. %a)" gen_term e' gen_term e
            | "op_mul"      -> fprintf ppf "(%a *. %a)" gen_term e' gen_term e
            | "op_div"      -> fprintf ppf "(%a /. %a)" gen_term e' gen_term e
            | "string_concat" -> fprintf ppf "(%a ^ %a)" gen_term e' gen_term e
            | _             -> fprintf ppf "(@[%a@ %a@])" gen_term f gen_term e
          end
        | _ -> fprintf ppf "(@[%a@ %a@])" gen_term f gen_term e
      end
    | TmAbs (_, b, _sty, _t2, body) ->
      fprintf ppf "(fun %s ->@\n @[%a@])" (ml_b b) gen_term body

    | TmAmpersand (_i, e1, e2) -> fprintf ppf "(%a,%a)" gen_term e1 gen_term e2

    (* let bi = e1 in e2 *)
    | TmLet (_, bi, _si, e1, e2) ->
      begin
        match e1 with
        | TmPrim(_, PrimTFun(_, _)) -> gen_term ppf e2
        | _ -> fprintf ppf "(let %s = %a in@\n%a)" (ml_b bi) gen_term e1 gen_term e2
      end

    | TmLetRec (_, bi, _ty, e1, e2) ->
      fprintf ppf "(let rec %s = %a in@\n%a)" (ml_b bi) gen_term e1 gen_term e2

    | TmSample (_, bi, e1, e2) ->
      fprintf ppf "(p_sample %a (fun %s -> %a))" gen_term e1 (ml_b bi) gen_term e2

    (* Empty as of now *)
    | TmTypedef (_i,_tn,_ty,tm) -> gen_term ppf tm
    | TmUnfold (_i, tm) -> gen_term ppf tm
      (* fprintf ppf "(m_unfold %a)" gen_term tm *)
    | TmFold(_i, _ty, tm) -> gen_term ppf tm
      (* fprintf ppf "(m_fold [%a] %a)" pp_type ty gen_term tm *)

    (* In OCaml, for both cases we just ignore it *)
    | TmTyAbs(_i, _b, _k, tm)      -> gen_term ppf tm
    | TmTyApp(_i, tm, _ty)         -> gen_term ppf tm

    (* TODO: DFuzz *)
    | TmSiApp(_,_,_)         -> fprintf ppf "XXX TODO: TmInst"

    | TmListCase (_) -> fprintf ppf "XXX TODO list case"
    | TmNatCase (_)  -> fprintf ppf "XXX TODO nat case"

    | TmUnpack(_,_,_,_,_)    -> fprintf ppf "XXX TODO: TmUnpack"
    | TmPack(_,_,_,_)        -> fprintf ppf "XXX TODO: TmPack"

let gen_program ppf t =
  fprintf ppf "%s@\n" header;
  gen_term ppf t;
  fprintf ppf "%s@." body

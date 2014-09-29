/* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*/
%{

open Syntax

open Support.FileInfo

let parser_error   fi = Support.Error.error_msg   Support.Options.Parser fi
let parser_warning fi = Support.Error.message   1 Support.Options.Parser fi
let parser_info    fi = Support.Error.message   2 Support.Options.Parser fi

let si_zero  = SiConst 0.0
let si_one   = SiConst 1.0
let si_infty = SiInfty
let dummy_ty  = TyPrim PrimUnit

let rec int_to_speano n = if n = 0 then SiZero else SiSucc (int_to_speano (n-1))

(* look for a variable in the current context *)
let existing_var fi id ctx =
  match Ctx.lookup_var id ctx with
      None            -> parser_error fi "Identifier %s is unbound" id
    | Some (var, _bi) -> var

let existing_tyvar fi id ctx =
  match Ctx.lookup_tyvar id ctx with
      None            -> parser_error fi "Type %s is unbound" id
    | Some (var, bi)  -> (var, bi)

(* Wrap extend here in order to avoid mutually recursive
   dependencies *)
let extend_var id ctx =
  Ctx.extend_var id dummy_ty ctx

let extend_ty_var id ki ctx =
  Ctx.extend_ty_var id ki ctx

(* Create a new binder *)
(* TODO: set the proper b_size !!! *)
let nb_prim  n = {b_name = n; b_type = BiVar;   b_size = -1; b_prim = true;}
let nb_var   n = {b_name = n; b_type = BiVar;   b_size = -1; b_prim = false;}
let nb_tyvar n = {b_name = n; b_type = BiTyVar; b_size = -1; b_prim = false;}

(* From a list of arguments to a type *)
let rec qf_to_type qf ty = match qf with
    []               -> ty
  | (_, n, k) :: qfl -> TyForall(nb_tyvar n, k, qf_to_type qfl ty)

let rec list_to_type l ret_ty = match l with
    []                        -> TyLollipop (TyPrim PrimUnit, si_infty, ret_ty) (* Not yet allowed constant function *)
  | (ty, si, _n, _i) :: []    -> TyLollipop (ty, si, ret_ty)
  | (ty, si, _n, _i) :: tyl   -> TyLollipop (ty, si, list_to_type tyl ret_ty)

let from_args_to_type qf arg_list ret_ty =
  qf_to_type qf (list_to_type arg_list ret_ty)

(* From a list of arguments to a term *)
let rec qf_to_term qf tm = match qf with
    []               -> tm
  | (i, n, k) :: qfl ->
      TmTyAbs (i, nb_tyvar n, k, qf_to_term qfl tm)

let rec list_to_term l body = match l with
    []                    -> body
  | (ty, si, n, i) :: tml -> TmAbs (i, nb_var n, (si, ty), None, list_to_term tml body)

let from_args_to_term qf arg_list body =
  qf_to_term qf (list_to_term arg_list body)

let mk_infix ctx info op t1 t2 =
  match Ctx.lookup_var op ctx with
      None      -> parser_error info "The primitive infix operator %s is not in scope" op
    | Some(v,_) -> TmApp(info, TmApp(info, TmVar(info, v), t1), t2)

(* This takes a *reversed* list of arguments *)
let rec mk_prim_app_args info v arglist = match arglist with
  | []        -> v
  | (o :: op) -> TmApp(info, (mk_prim_app_args info v op), o)

let mk_prim_app ctx info prim arglist =
  match Ctx.lookup_var prim ctx with
    None      -> parser_error info "Primitive %s is not in scope" prim
  | Some(v,_) -> mk_prim_app_args info (TmVar(info, v)) (List.rev arglist)

let rec mk_prim_app_ty_args info v arglist = match arglist with
  | []        -> v
  | (o :: op) -> TmTyApp(info, (mk_prim_app_ty_args info v op), o)

let mk_prim_ty_app ctx info prim arglist =
  match Ctx.lookup_var prim ctx with
    None      -> parser_error info "Primitive %s is not in scope" prim
  | Some(v,_) -> mk_prim_app_ty_args info (TmVar(info, v)) (List.rev arglist)

let mk_lambda info bi oty term = TmAbs(info, bi, oty, None, term)

let rec remove_quantifiers ty = match ty with
    TyForall(_,_,ty_i) -> remove_quantifiers ty_i
  | _ -> ty

%}

/* ---------------------------------------------------------------------- */
/* Preliminaries */

/* Keyword tokens */
%token <Support.FileInfo.info> AT
%token <Support.FileInfo.info> ADD
%token <Support.FileInfo.info> AMP
%token <Support.FileInfo.info> AND
%token <Support.FileInfo.info> ARROW
%token <Support.FileInfo.info> COLON
%token <Support.FileInfo.info> CONS
%token <Support.FileInfo.info> COMMA
%token <Support.FileInfo.info> DOLLAR
%token <Support.FileInfo.info> LBRACE
%token <Support.FileInfo.info> QUESTION
%token <Support.FileInfo.info> SEMI
%token <Support.FileInfo.info> RBRACE
%token <Support.FileInfo.info> EQUAL
%token <Support.FileInfo.info> HAT
%token <Support.FileInfo.info> BEQUAL
%token <Support.FileInfo.info> DBLARROW
%token <Support.FileInfo.info> SUB
%token <Support.FileInfo.info> MUL
%token <Support.FileInfo.info> DIV
%token <Support.FileInfo.info> LPAREN
%token <Support.FileInfo.info> RPAREN
%token <Support.FileInfo.info> LT
%token <Support.FileInfo.info> GT
%token <Support.FileInfo.info> LBRACK
%token <Support.FileInfo.info> RBRACK
%token <Support.FileInfo.info> PIPE
%token <Support.FileInfo.info> OR
%token <Support.FileInfo.info> BANG
%token <Support.FileInfo.info> LOLLIPOP
%token <Support.FileInfo.info> TRUE
%token <Support.FileInfo.info> FALSE
%token <Support.FileInfo.info> INF
%token <Support.FileInfo.info> INL
%token <Support.FileInfo.info> INR
%token <Support.FileInfo.info> FUZZY
%token <Support.FileInfo.info> FUN
%token <Support.FileInfo.info> UNIONCASE
%token <Support.FileInfo.info> LISTCASE
%token <Support.FileInfo.info> NUMCASE
%token <Support.FileInfo.info> OF
%token <Support.FileInfo.info> FOLD
%token <Support.FileInfo.info> UNFOLD
%token <Support.FileInfo.info> MU
%token <Support.FileInfo.info> LET
%token <Support.FileInfo.info> TYPEDEF
%token <Support.FileInfo.info> SAMPLE
%token <Support.FileInfo.info> FUNCTION
%token <Support.FileInfo.info> PRIMITIVE
%token <Support.FileInfo.info> SET
%token <Support.FileInfo.info> BAG
%token <Support.FileInfo.info> IF
%token <Support.FileInfo.info> THEN
%token <Support.FileInfo.info> ELSE
%token <Support.FileInfo.info> PRINT
%token <Support.FileInfo.info> EOF
%token <Support.FileInfo.info> BOOL
%token <Support.FileInfo.info> NUM
%token <Support.FileInfo.info> STRING
%token <Support.FileInfo.info> SIZE
%token <Support.FileInfo.info> SENS
%token <Support.FileInfo.info> TYPE
%token <Support.FileInfo.info> PACK
%token <Support.FileInfo.info> WITH
%token <Support.FileInfo.info> IN
%token <Support.FileInfo.info> FOR
%token <Support.FileInfo.info> UNPACK
%token <Support.FileInfo.info> FUZZ
%token <Support.FileInfo.info> FUZZB
%token <Support.FileInfo.info> PRIMITER
%token <Support.FileInfo.info> FORALL
%token <Support.FileInfo.info> EXISTS
%token <Support.FileInfo.info> LIST
%token <Support.FileInfo.info> DBLCOLON
%token <Support.FileInfo.info> NAT
%token <Support.FileInfo.info> CLIPPED
%token <Support.FileInfo.info> DBSOURCE
%token <Support.FileInfo.info> INT
%token <Support.FileInfo.info> DOT
%token <Support.FileInfo.info> ZERO
%token <Support.FileInfo.info> SUCC

/* Identifier and constant value tokens */
%token <string Support.FileInfo.withinfo> ID
%token <int    Support.FileInfo.withinfo> INTV
%token <float  Support.FileInfo.withinfo> FLOATV
%token <string Support.FileInfo.withinfo> STRINGV

/* ---------------------------------------------------------------------- */
/* Fuzz grammar                                                           */
/* ---------------------------------------------------------------------- */

%start body
%type < Syntax.term > body
%%

/* ---------------------------------------------------------------------- */
/* Main body of the parser definition                                     */
/* ---------------------------------------------------------------------- */

body :
    Term EOF
      { $1 Ctx.empty_context }

PrimSpec :
    STRINGV
      { $1 }

Term :
    ID SensAnn EQUAL Expr SEMI Term
      {
        fun ctx ->
          let ctx' = extend_var $1.v ctx in
          TmLet($1.i, (nb_var $1.v), $2 ctx, $4 ctx, $6 ctx')
      }
  /* | LET LPAREN ID COMMA ID RPAREN SensAnn EQUAL Expr SEMI Term */
  | LET LPAREN ID COMMA ID RPAREN EQUAL Expr SEMI Term
      { fun ctx ->
        (* TODO, what happens with let (x,x) = ...? *)
        let ctx_x  = extend_var $3.v ctx   in
        let ctx_xy = extend_var $5.v ctx_x in
        TmTensDest($1, (nb_var $3.v), (nb_var $5.v), $8 ctx, $10 ctx_xy)
      }
  | SAMPLE ID EQUAL Expr SEMI Term
      { fun ctx ->
        TmSample ($2.i, (nb_var $2.v), $4 ctx, $6 (extend_var $2.v ctx))
      }
  | TYPEDEF ID EQUAL Type SEMI Term
      {
        fun ctx ->
        TmTypedef($1, (nb_tyvar $2.v), $4 ctx, $6 (extend_ty_var $2.v Star ctx))
      }
  | PRIMITIVE ID Quantifiers Arguments COLON Type LBRACE PrimSpec RBRACE Term
      { fun ctx ->
        let (qf,   ctx_qf)   = $3 ctx                                              in
        let (args, ctx_args) = $4 ctx_qf                                           in
        let f_type           = from_args_to_type qf args ($6 ctx_args)             in
        let ctx_f_outer      = extend_var $2.v ctx                                 in
        let tm_prim          = TmPrim($8.i, PrimTFun($8.v, f_type))                in
        TmLet($1, (nb_prim $2.v), si_infty, tm_prim, $10 ctx_f_outer)
      }
  | FUNCTION ID Quantifiers Arguments COLON Type LBRACE Term RBRACE Term
      {
        fun ctx ->
        let ctx_let          = extend_var $2.v ctx        in
        let (qf,   ctx_qf)   = $3 ctx_let                 in
        let (args, ctx_args) = $4 ctx_qf                  in
        let f_type           = from_args_to_type qf args ($6 ctx_args) in
        let f_term           = from_args_to_term qf args ($8 ctx_args) in

        TmLetRec($2.i, nb_var $2.v, f_type, f_term, $10 ctx_let)
      }
/*
  | UNPACK SIZE LPAREN ID COMMA ID RPAREN EQUAL Expr SEMI Term
      { fun ctx ->
        let ctx' = extend_var $4.v ctx in
        let ctx'' = extend_ty_var $6.v Size ctx' in
        TmUnpack($1, nb_var $4.v, nb_tyvar $6.v, $9 ctx, $11 ctx'') }

  | UNPACK SENS LPAREN ID COMMA ID RPAREN EQUAL Expr SEMI Term
      { fun ctx ->
        let ctx' = extend_var $4.v ctx in
        let ctx'' = extend_ty_var $6.v Sens ctx' in
        TmUnpack($1, nb_var $4.v, nb_tyvar $6.v, $9 ctx, $11 ctx'') }
*/
  | LogOrTerm
      { $1 }

Argument :
    LPAREN ID COLON MaybeSensitivity Type RPAREN
      { fun ctx -> ([($5 ctx, $4 ctx, $2.v, $2.i)], extend_var $2.v ctx) }

/*
   Arguments returns a tuple of (arg, ctx), where arg is the list of
   arguments ready to build a higher-order type, including quantifiers.
*/
Arguments :
    Argument
      { $1 }
  | Argument Arguments
      { fun ctx ->
          let (l,  ctx')  = $1 ctx in
          let (l2, ctx'') = $2 ctx' in
          (l @ l2, ctx'')
      }

Expr :
      LogOrTerm
      { $1 }

LogOrTerm :
    LogOrTerm OR LogAndTerm
      { fun ctx -> mk_infix ctx $2 "op_lor" ($1 ctx) ($3 ctx) }
  | LogAndTerm
      { $1 }

LogAndTerm:
    LogAndTerm AND BequalTerm
      { fun ctx -> mk_infix ctx $2 "op_land" ($1 ctx) ($3 ctx) }
  | BequalTerm
      { $1 }

BequalTerm :
    BequalTerm BEQUAL RelTerm
      { fun ctx -> mk_infix ctx $2 "op_eq" ($1 ctx) ($3 ctx) }
  | BequalTerm BANG EQUAL RelTerm
      { fun ctx -> mk_infix ctx $2 "op_neq" ($1 ctx) ($4 ctx) }
  | RelTerm
      { $1 }

RelTerm :
    RelTerm LT AddTerm
      { fun ctx -> mk_infix ctx $2 "op_lt" ($1 ctx) ($3 ctx) }
  | RelTerm GT AddTerm
      { fun ctx -> mk_infix ctx $2 "op_gt" ($1 ctx) ($3 ctx) }
  | RelTerm LT EQUAL AddTerm
      { fun ctx -> mk_infix ctx $2 "op_lte" ($1 ctx) ($4 ctx) }
  | RelTerm GT EQUAL AddTerm
      { fun ctx -> mk_infix ctx $2 "op_gte" ($1 ctx) ($4 ctx) }
  | AddTerm
      { $1 }

AddTerm :
    AddTerm ADD MulTerm
      { fun ctx -> mk_infix ctx $2 "op_add" ($1 ctx) ($3 ctx) }
  | AddTerm DOT ADD MulTerm
      { fun ctx -> mk_infix ctx $2 "op_iadd" ($1 ctx) ($4 ctx) }
  | AddTerm HAT MulTerm
      { fun ctx -> mk_infix ctx $2 "string_concat" ($1 ctx) ($3 ctx) }
  | AddTerm SUB MulTerm
      { fun ctx -> mk_infix ctx $2 "op_sub" ($1 ctx) ($3 ctx) }
  | AddTerm DOT SUB MulTerm
      { fun ctx -> mk_infix ctx $2 "op_isub" ($1 ctx) ($4 ctx) }
  | MulTerm
      { $1 }

MulTerm :
    MulTerm MUL FTerm
      { fun ctx -> mk_infix ctx $2 "op_mul" ($1 ctx) ($3 ctx) }
  | MulTerm DIV FTerm
      { fun ctx -> mk_infix ctx $2 "op_div" ($1 ctx) ($3 ctx) }
  | FTerm
      { $1 }

FTerm :
  | FOLD LBRACK Type RBRACK STerm
      { fun ctx -> TmFold($1, $3 ctx, $5 ctx) }
  | UNFOLD STerm
      { fun ctx -> TmUnfold($1, $2 ctx) }
  | STerm
      { $1 }

STerm :
    IF Expr THEN LBRACK Type RBRACK LBRACE Term RBRACE ELSE LBRACE Term RBRACE
      { fun ctx ->
        let if_then_spec = mk_prim_ty_app ctx $1 "if_then_else" [$5 ctx] in
        let arg_list    = [$2 ctx;
                           TmAmpersand($6,
                                       mk_lambda $7  (nb_var "thunk") (si_one, TyPrim PrimUnit) ($8  (extend_var "_" ctx)),
                                       mk_lambda $11 (nb_var "thunk") (si_one, TyPrim PrimUnit) ($12 (extend_var "_" ctx)));] in
        mk_prim_app_args $1 if_then_spec (List.rev arg_list)
      }

/*  | PACK SIZE Expr WITH SizeTerm FOR ID IN Type
      { fun ctx ->
        let ctx' = extend_ty_var $7.v Size ctx in
        TmPack($1, $3 ctx, $5 ctx, TyExistsSize (nb_tyvar $7.v, $9 ctx')) }
*/

  /* Fixme: Reflect type */
  /* Fixme: Read return annotation */
  /* EG: Leaving untouched until I can figure it out what is going out with this rule */
  | UNIONCASE Expr OF SensAnn LBRACE INL LPAREN ID RPAREN DBLARROW Term PIPE INR LPAREN ID RPAREN DBLARROW Term RBRACE
      { fun ctx ->
        let ctx_l = extend_var $8.v  ctx in
        let ctx_r = extend_var $15.v ctx in
        TmUnionCase($1, $2 ctx, $4 ctx, dummy_ty, nb_var $8.v, $11 ctx_l, nb_var  $15.v, $18 ctx_r) }

  | LISTCASE Expr OF Type LBRACE LBRACK RBRACK DBLARROW Term PIPE ID DBLCOLON ID LBRACK ID RBRACK DBLARROW Term RBRACE
      { fun ctx ->
        let ctx_l  = extend_var    $11.v      ctx    in
        let ctx_ll = extend_var    $13.v      ctx_l  in
        let ctx_si = extend_ty_var $15.v Sens ctx_ll in
        TmListCase($1, $2 ctx, $4 ctx, $9 ctx, nb_var $11.v, nb_var $13.v, nb_var $15.v, $18 ctx_si) }

  | NUMCASE Expr OF Type LBRACE ZERO DBLARROW Term PIPE SUCC ID LBRACK ID RBRACK DBLARROW Term RBRACE
      { fun ctx ->
        (* Todo: here we could guess more of dependent type *)
        let ctx_n = extend_var    $11.v      ctx   in
        let ctx_s = extend_ty_var $13.v Size ctx_n in
        TmNatCase($1, $2 ctx, $4 ctx, $8 ctx, nb_var $11.v, nb_tyvar $13.v, $16 ctx_s)
      }
  | FUN LPAREN ID SensType RPAREN MaybeType LBRACE Term RBRACE
      { fun ctx -> TmAbs($1, nb_var $3.v, $4 ctx, $6 ctx, $8 (extend_var $3.v ctx )) }
  | FExpr
      { $1 }

FExpr :
    SFExpr
      { $1 }
  | FExpr SFExpr
      { fun ctx -> let e1 = $1 ctx in let e2 = $2 ctx in TmApp(tmInfo e1, e1, e2) }

/* Sensitivity application */
SFExpr:
    TFExpr
      { $1 }
  | SFExpr LBRACK SensTerm RBRACK
      { fun ctx -> TmSiApp($2, $1 ctx, $3 ctx) }

/* Type application */
TFExpr:
    AExpr
      { $1 }
  | TFExpr AT LBRACK Type RBRACK
      { fun ctx -> TmTyApp($2, $1 ctx, $4 ctx) }

/* Sugar for n-ary tuples */
PairSeq:
    Term COMMA Term
      { fun ctx -> TmPair($2, $1 ctx, $3 ctx)  }
  | Term COMMA PairSeq
      { fun ctx -> TmPair($2, $1 ctx, $3 ctx)  }

AExpr:
    TRUE
      { fun _cx -> TmPrim ($1, PrimTBool true) }
  | FALSE
      { fun _cx -> TmPrim ($1, PrimTBool false) }
  | LPAREN RPAREN
      { fun _cx -> TmPrim ($1, PrimTUnit) }
  | ID
      { fun ctx -> TmVar($1.i, existing_var $1.i $1.v ctx) }
  | INL
      { fun ctx -> mk_prim_app ctx $1 "p_inl" []  }
  | INR
      { fun ctx -> mk_prim_app ctx $1 "p_inr" []  }
  | LPAREN Term RPAREN
      { $2 }
  | LPAREN PairSeq RPAREN
      { fun ctx -> $2 ctx }
  | LPAREN PIPE Term COMMA Term PIPE RPAREN
      { fun ctx -> TmAmpersand($1, $3 ctx, $5 ctx) }
  | STRINGV
      { fun _cx -> TmPrim($1.i, PrimTString $1.v) }
  | FLOATV
      { fun _cx -> TmPrim($1.i, PrimTNum $1.v) }
  | INTV
      { fun _cx -> TmPrim($1.i, PrimTInt $1.v) }

/* Sensitivities and sizes */
SensTerm :
    SensTerm ADD SensMulTerm
      { fun ctx -> SiAdd($1 ctx, $3 ctx) }
  | SensMulTerm
      { $1 }

SensMulTerm :
    SensMulTerm MUL SensAtomicTerm
      { fun ctx -> SiMult($1 ctx, $3 ctx) }
  | SensAtomicTerm
      { $1 }

SizeTerm :
    ID
      { fun ctx -> let (v, k) = existing_tyvar $1.i $1.v ctx in
                   match k with
                   | Star -> parser_error $1.i "Cannot bind a type variable in sensitivity"
                   | Sens -> parser_error $1.i "Cannot bind a sens variable in a size"
                   | Size -> (SiVar v)
      }
  | ZERO
      { fun _cx ->
        SiZero
      }
  | SUCC SizeTerm
      { fun ctx ->
        SiSucc ($2 ctx)
      }

SensAtomicTerm :
    ID
      { fun ctx -> let (v, k) = existing_tyvar $1.i $1.v ctx in
                   match k with
                   | Star -> parser_error $1.i "Cannot bind a type variable in sensitivity"
                   | _    -> SiVar v
      }
  | INTV
      { fun _cx ->
        (int_to_speano $1.v)
      }
  | FLOATV
      { fun _cx -> SiConst $1.v }

SensType :
  | COLON MaybeSensitivity Type
      { fun ctx -> ($2 ctx, $3 ctx) }

SensAnn :
  | COLON MaybeSensitivity
      { fun ctx -> $2 ctx }

MaybeSensitivity:
    /* nothing */
      { fun _cx -> si_infty }
  | LBRACK RBRACK
      { fun _cx -> SiConst 1.0 }
  | LBRACK SensTerm RBRACK
      { $2 }

/* Binding type */
Kind :
    SIZE
      { Size }
  | TYPE
      { Star }
  | SENS
      { Sens }

KindAnn :
    ID
      { fun ctx -> ([($1.i, $1.v, Star)], extend_ty_var $1.v Star ctx) }
  | ID COLON Kind
      { fun ctx -> ([($1.i, $1.v, $3)],   extend_ty_var $1.v $3 ctx) }

QuantifierList :
    KindAnn
      { $1 }
  | KindAnn COMMA QuantifierList
      { fun ctx -> let (tyv, ctx')  = $1 ctx  in
                   let (qf, ctx_qf) = $3 ctx' in
                   (tyv @ qf, ctx_qf)
      }

Quantifiers :
  /* Nothing */
    { fun ctx -> ([], ctx) }
  | FORALL LPAREN QuantifierList RPAREN
    { $3 }

MaybeType:
    {fun _ctx -> None}
  | COLON Type
      {fun ctx -> Some ($2 ctx)}

Type :
    AType SET
      { fun ctx -> TyPrim1 (Prim1Set, ($1 ctx)) }
  | AType BAG
      { fun ctx -> TyPrim1 (Prim1Bag, ($1 ctx)) }
  | NAT LBRACK SizeTerm RBRACK
      { fun ctx -> TySizedNat($3 ctx) }
  | NUM LBRACK SensTerm RBRACK
      { fun ctx -> TySizedNum($3 ctx) }
  | MU ID DBLARROW Type
      { fun ctx -> TyMu(nb_tyvar $2.v, $4 (extend_ty_var $2.v Star ctx)) }
  | ComplexType
      { $1 }

ComplexType :
    AType ARROW ComplexType
      { fun ctx -> TyLollipop($1 ctx, si_infty, $3 ctx) }
  | AType ADD ComplexType
      { fun ctx -> TyUnion($1 ctx, $3 ctx) }
  | AType LOLLIPOP ComplexType
      { fun ctx -> TyLollipop($1 ctx, SiConst 1.0, $3 ctx) }
  | AType LOLLIPOP LBRACK SensTerm RBRACK ComplexType
      { fun ctx -> TyLollipop($1 ctx, $4 ctx, $6 ctx) }
  | FUZZY Type
      { fun ctx -> TyPrim1 (Prim1Fuzzy, ($2 ctx)) }
  | LIST LPAREN Type RPAREN LBRACK SizeTerm RBRACK
      { fun ctx -> TyList($3 ctx, $6 ctx) }
  | AType
      { $1 }

TPairSeq:
    Type COMMA Type
      { fun ctx -> TyTensor($1 ctx, $3 ctx) }
  | Type COMMA TPairSeq
      { fun ctx -> TyTensor($1 ctx, $3 ctx) }

AType :
    LPAREN Type RPAREN
      { $2 }
  | ID
      {	fun ctx -> let (v, _) = existing_tyvar $1.i $1.v ctx in
                   TyVar v
      }
  | BOOL
      { fun _cx -> TyPrim PrimBool }
  | NUM
      { fun _cx -> TyPrim PrimNum }
  | INT
      { fun _cx -> TyPrim PrimInt }
  | STRING
      { fun _cx -> TyPrim PrimString }
  | CLIPPED
      { fun _cx -> TyPrim PrimClipped }
  | DBSOURCE
      { fun _cx -> TyPrim PrimDBS }
  | LPAREN RPAREN
      { fun _cx -> TyPrim PrimUnit }
  | LPAREN TPairSeq RPAREN
      { fun ctx -> $2 ctx }
  | LPAREN PIPE Type COMMA Type PIPE RPAREN
      { fun ctx -> TyAmpersand($3 ctx, $5 ctx) }

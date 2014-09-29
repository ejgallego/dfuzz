(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   Copyright (c) 2013, The IMDEA Software Institute
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

module WC = WhyCore
module WT = WhyTrans

open Why3
module CP = Call_provers

open Support.Error

module Opts = Support.Options

(* Native @@ is already in ocaml 4.0 *)
let (@@) x y = x y

let dp = Support.FileInfo.dummyinfo

let why_error   fi   = error_msg Opts.SMT fi

let why_warning fi   = message 1 Opts.SMT fi
let why_info    fi   = message 2 Opts.SMT fi
let why_info2   fi   = message 3 Opts.SMT fi
let why_debug   fi   = message 4 Opts.SMT fi
let why_debug2  fi   = message 5 Opts.SMT fi
let why_debug3  fi   = message 6 Opts.SMT fi

(* We will likely borrow the EC implementation for this file *)

let alt_ergo : Whyconf.config_prover =
  let fp = Whyconf.parse_filter_prover "Alt-Ergo"   in
  (** all provers that have the name "Alt-Ergo" *)
  let provers = Whyconf.filter_provers WC.config fp in
  if Whyconf.Mprover.is_empty provers then begin
    Format.eprintf "Prover Alt-Ergo not installed or not configured@.";
    exit 0
  end else
    snd (Whyconf.Mprover.max_binding provers)

(* loading the Alt-Ergo driver *)
let alt_ergo_driver : Driver.driver =
  try
    Driver.load_driver WC.env alt_ergo.Whyconf.driver []
  with e ->
    Format.eprintf "Failed to load driver for alt-ergo: %a@."
      Exn_printer.exn_printer e;
    exit 1

let post cs =
  let task    = None                                                   in
  let goal_id = Decl.create_prsymbol (Ident.id_fresh "ty_goal")        in
  let task    = Task.use_export task WT.int_theory                     in
  (* let task    = Task.use_export task WT.dfuzz_i_theory                 in *)
  let task    = Task.use_export task WT.real_theory                    in
  let task    = Task.use_export task WT.dfuzz_theory                   in
  (* let task    = Task.use_export task WT.fin_theory                     in *)
  (* let task    = Task.use_export task WT.list_theory                    in *)
  (* let task    = Task.use_export task WT.exp_theory                     in *)
  (* let task    = Task.use_export task WT.dp_theory                      in *)
  let task    = Task.add_prop_decl task Decl.Pgoal goal_id cs          in

  why_info   dp "calling solver....";
  why_debug3 dp "why3 task is: @[@\n%a@]@." Pretty.print_task task;

  let result : Call_provers.prover_result =
    Call_provers.wait_on_call
      (Driver.prove_task ~command:alt_ergo.Whyconf.command ~timelimit:60
  	 alt_ergo_driver task ()) ()                                   in

  why_info dp "@[alt-ergo answers %a@]@." Call_provers.print_prover_result result;
  match result.CP.pr_answer with
  | CP.Valid   -> true
  | CP.Invalid -> false
  | _          -> false
  (* | Timeout *)
  (*     (\** the task timeout, ie it takes more time than specified *\) *)
  (* | OutOfMemory *)
  (*     (\** the task timeout, ie it takes more time than specified *\) *)
  (* | Unknown of string *)
  (*     (\** The prover can't determine if the task is valid *\) *)
  (* | Failure of string *)
  (*     (\** The prover reports a failure *\) *)
  (* | HighFailure *)
  (*     (\** An error occured during the call to the prover or none *)
  (*         of the given regexps match the output of the prover *\) *)


(* Send to Why3 *)
open Constr

let send_smt cs =
  let i       = cs.c_info                            in
  let why3_cs = WT.why3_translate cs                 in

  why_info i "!*! Solving Constraint: @[%a@]" Print.pp_cs cs;
  why_debug i "!*! Why3 term: @[%a@]"  Why3.Pretty.print_term why3_cs;
  why_debug i "!*! -----------------------------------------------";

  if Opts.comp_enabled Opts.SMT then
    post why3_cs
  else
    true

(* let test6 () = *)
(*   printf "@[task 2 is:@\n%a@]@." Pretty.print_task task2; *)
(*   printf "@[On task 2, alt-ergo answers %a in %5.2f seconds@." *)
(*     Call_provers.print_prover_answer *)
(*     result2.Call_provers.pr_answer *)
(*     result2.Call_provers.pr_time *)


(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
module Options = struct

  (* Are we running in dependent mode? *)
  let dfuzz_enabled = ref false

  (* Components of the compiler *)
  type component =
  | General
  | Lexer
  | Parser
  | TypeChecker
  | SMT
  | Backend

  let default_components =
    [Lexer; Parser; TypeChecker; SMT]
    (* [Lexer; Parser; TypeChecker; Backend] *)

  let components = ref default_components

  let comp_enabled comp =
    List.mem comp !components

  let comp_disable comp =
    let (_, l) = List.partition (fun c -> c = comp) !components in
    components := l

  (* Pretty printing options *)
  type pr_vars =
      PrVarName
    | PrVarIndex
    | PrVarBoth

  type debug_options = {
    components   : component list;
    level        : int;     (* Printing level *)
    unicode      : bool;    (* Use unicode output  *)
    pr_ann       : bool;    (* Print type annotations in the expressions *)
    pr_level     : int;     (* Default printing depth *)
    var_output   : pr_vars; (* Ouput names of vars *)
    full_context : bool;    (* Only names in ctx   *)
  }

  let debug_default = {
    components   = [General;Lexer;Parser;TypeChecker;SMT;Backend];
    level        = 2;
    unicode      = true;
    pr_ann       = true;
    pr_level     = 8;
    var_output   = PrVarName;
    full_context = true;
  }

  let debug_options = ref debug_default;
end

module FileInfo = struct

  type info = FI of string * int * int | UNKNOWN
  type 'a withinfo = {i: info; v: 'a}

  let dummyinfo = UNKNOWN
  let createInfo f l c = FI(f, l, c)

  let pp_fileinfo ppf = function
    | FI(f,l,c) -> let f_l = String.length f   in
                   let f_t = min f_l 12        in
                   let f_s = max 0 (f_l - f_t) in
                   let short_file = String.sub f f_s f_t in
                   Format.fprintf ppf "(%s:%02d.%02d)" short_file l c
    | UNKNOWN   -> Format.fprintf ppf ""

  let file_ignored_list =
    ["./lib/primitives.fz";
     "examplese/fuzz/tutorial/library-lists.fz";
     "examplese/fuzz/tutorial/library-bags.fz";
    ]

  let file_ignored fi = match fi with
    | UNKNOWN   -> false
    | FI(f,_,_) -> List.mem f file_ignored_list

end

module Error = struct

  open Options

  exception Exit of int

  (* Printing levels:
        0  Error
        1  warning
        2  Info
        3+ Debug.

     Debug levels:

     3: Print rules executed and return types.
     4: Print rules executed, return types, constraint store and context.
     5: Print everything, including detailed stuff about type eq and unification, context merging, etc...
     6: Print everything, including optimizations.
  *)

  let comp_to_string = function
    | General     -> "[General]"
    | Lexer       -> "[Lexer  ]"
    | Parser      -> "[Parser ]"
    | TypeChecker -> "[TyCheck]"
    | SMT         -> "[SMT    ]"
    | Backend     -> "[Backend]"

  let level_to_string = function 
    | 0 -> "Error  "
    | 1 -> "Warning"
    | 2 -> "Info   "
    | 3 -> "Info+  "
    | 4 -> "Debug 1"
    | 5 -> "Debug 2"
    | 6 -> "Debug 3"
    | 7 -> "Debug 4"
    | _ -> ""

  let level_to_string = function
    | 0 -> "E "
    | 1 -> "W "
    | 2 -> "I "
    | 3 -> "I+"
    | 4 -> "D1"
    | 5 -> "D2"
    | 6 -> "D3"
    | 7 -> "D4"
    | _ -> ""

  (* Default print function *)
  let message level component fi =
    if level <= !debug_options.level &&
      List.mem component !debug_options.components &&
      not (FileInfo.file_ignored fi) then
      begin
	Format.eprintf "@[%s %s %a: @[" (level_to_string level) (comp_to_string component) FileInfo.pp_fileinfo fi;
	Format.kfprintf (fun ppf -> Format.fprintf ppf "@]@]@.") Format.err_formatter
      end
    else
      Format.ifprintf Format.err_formatter

(* XXX: Note the caveat that the eprintf here will be executed *)
  let error_msg comp fi =
    let cont _ =
      Format.eprintf "@]@.";
      raise (Exit 1)                in
    Format.eprintf "@[%s %s %a: " (level_to_string 0) (comp_to_string comp) FileInfo.pp_fileinfo fi;
    Format.kfprintf cont Format.err_formatter

  let error_msg_pp comp fi pp v =
    Format.eprintf "@[%s %s %a: %a@." (level_to_string 0) (comp_to_string comp)
      FileInfo.pp_fileinfo fi pp v;
    raise (Exit 1)

end

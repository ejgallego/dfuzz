(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   and PLEAC

   LICENSE:
   Based on PLEAC, adapted to use COLUMNS and tput

*)

(* Here we include general library and utility functions, not directly
   related to fuzz.

   In an ideal world they should be removed and the corresponding
   existing libraries used.
*)

let get_terminal_size () =

  (* let in_channel = Unix.open_process_in "tput cols" in *)
  let in_channel = Unix.open_process_in "stty size" in
  try
    begin
      try
        Scanf.fscanf in_channel "%d %d"
          (fun rows cols ->
             ignore (Unix.close_process_in in_channel);
             (rows, cols))
      with End_of_file ->
        ignore (Unix.close_process_in in_channel);
        (0, 0)
    end
  with e ->
    ignore (Unix.close_process_in in_channel);
    raise e

  (* Note that the COLUMNS solution is not a good idea as it is a BASH
     builtin wrapper for tput, however it does allow us to don't
     require tput or stty *)
  (* try int_of_string (Sys.getenv "COLUMNS") *)

(* String.map not until Ocaml 4.00 *)
let map f s =

  let l = String.length s in

  if l = 0 then s else
    begin
      let r = String.create l in
      for i = 0 to l - 1 do String.unsafe_set r i (f(String.unsafe_get s i)) done;
      r
    end

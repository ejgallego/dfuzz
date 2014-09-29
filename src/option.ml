(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

(* Very simple utility functions *)
let map f = function
        | None -> None
        | Some v -> Some (f v)

let default d = function
  | None   -> d
  | Some v -> v

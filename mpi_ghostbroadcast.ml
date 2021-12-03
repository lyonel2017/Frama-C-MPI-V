(**************************************************************************)
(*  This file is part of MPI-V plug-in of Frama-C.                        *)
(*                                                                        *)
(*  Copyright (C) 2020 Lionel Blatter                                     *)
(*                                                                        *)
(*  Lionel Blatter <lionel.blatter@kit.edu>                               *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file LICENSE).                      *)
(**************************************************************************)

open Cil_types

let filter_require kf b =
  let aux r =
    let name = r.ip_content.tp_statement.pred_name in
    match name with
    | [] -> ()
    | h :: [] when String.equal h "danglingness_buf" ->
      Annotations.remove_requires Emitter.end_user kf r
    | _ -> ()
  in
  List.iter aux b.b_requires

let remove_danglingness_buf () =
  let kf = Globals.Functions.find_by_name "MPI_GIntBcast" in
  Annotations.iter_behaviors (fun _ -> filter_require kf ) kf

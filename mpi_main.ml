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

let add_priority_condition () =
  let kf = Globals.Functions.find_by_name "main" in
  let t1 = Logic_const.tvar (Cil.cvar_to_lvar (Mpi_utils.get_var "priority")) in
  let t2 = Logic_const.tinteger 2 in
  let p = Logic_const.prel (Req, t1, t2) in
  let post = Cil_types.Normal, Mpi_utils.make_pred p "priority_check" in
  Annotations.add_ensures MPI_V_options.emitter kf [post]

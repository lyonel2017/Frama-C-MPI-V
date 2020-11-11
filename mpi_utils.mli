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

val string_of_typ : Cil_types.typ -> string

class visitor_beh: Cil_types.typ -> Cil_types.varinfo list -> Visitor.generic_frama_c_visitor

val mpi_comm: unit -> Cil_types.typ

val mpi_status: unit -> Cil_types.typ

val mpi_datatype: unit -> Cil_types.typ

val ptr_of: Cil_types.typ -> Cil_types.typ

val const_of: Cil_types.typ -> Cil_types.typ

val mpi_to_cil_typ: Cil_types.exp -> Cil_types.typ

val exp_type_of_pointed: Cil_types.exp -> Cil_types.typ option

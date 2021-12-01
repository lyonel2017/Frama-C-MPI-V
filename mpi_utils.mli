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
val ptr_of: Cil_types.typ -> Cil_types.typ
val const_of: Cil_types.typ -> Cil_types.typ
val mpi_to_cil_typ: Cil_types.exp -> Cil_types.typ
val cil_typ_to_mpi_string : Cil_types.typ -> string
val exp_type_of_pointed: Cil_types.exp -> Cil_types.typ option
val return_type: Cil_types.logic_info -> Cil_types.logic_type

class visitor_beh: Cil_types.typ -> Cil_types.varinfo list -> Visitor.generic_frama_c_visitor

val get_type: string -> Cil_types.typ
val get_var: string -> Cil_types.varinfo
val get_l_info: string -> Cil_types.logic_info

val getFirst_get_type_protocol: unit -> Cil_types.term
val to_list: Cil_types.term -> Cil_types.term -> Cil_types.term
val integer_var: Cil_types.varinfo -> Cil_types.term
val tapp: string -> Cil_types.term list -> Cil_types.logic_label list -> Cil_types.term

val papp: string -> Cil_types.term list -> Cil_types.logic_label list -> Cil_types.predicate
val same_array: Cil_types.varinfo -> Cil_types.varinfo -> Cil_types.predicate
val reduce_protocol: unit -> Cil_types.predicate

val make_pred: Cil_types.predicate -> string -> Cil_types.identified_predicate

val update_spec: Cil_types.spec -> string -> Cil_types.identified_predicate list ->
  (Cil_types.termination_kind * Cil_types.identified_predicate) list -> Cil_types.spec

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

let function_name = "MPI_Scatter"

let generate_prototype t =
  let ftype = Mpi_gather.generate_function_type t in
  let name = function_name ^ "_" ^ (Mpi_utils.string_of_typ t) in
  name, ftype

let generate_spec t _ f : Cil_types.funspec =
  let kf = Globals.Functions.find_by_name function_name in
  let spec = Annotations.funspec kf in
  let spec = Visitor.visitFramacFunspec (new Mpi_utils.visitor_beh t f.sformals) spec in
  spec

module M =
struct
  module Hashtbl = Cil_datatype.Typ.Hashtbl
  type override_key = typ

  let function_name = function_name
  let well_typed_call = Mpi_gather.well_typed_call
  let key_from_call = Mpi_gather.key_from_call
  let retype_args = Mpi_gather.retype_args
  let generate_prototype = generate_prototype
  let generate_spec = generate_spec
  let args_for_original _ = Extlib.id
end

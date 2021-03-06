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

let function_name = "MPI_Allgather"

let generate_spec t _ f : Cil_types.funspec =
  let kf = Globals.Functions.find_by_name function_name in
  let spec = Annotations.funspec kf in
  let spec = Visitor.visitFramacFunspec (new Mpi_utils.visitor_beh t f.sformals) spec in
  spec

let generate_function_type t =
  let ret = Cil.intType in
  let ps =
    [
      ("sendbuf" , Mpi_utils.const_of(Mpi_utils.ptr_of t), []) ;
      ("sendcount", Cil.intType, []);
      ("sendtype", Mpi_utils.get_typ "MPI_Datatype", []);
      ("recvbuf" , Mpi_utils.ptr_of t, []) ;
      ("recvcount", Cil.intType, []);
      ("recvtype", Mpi_utils.get_typ "MPI_Datatype", []);
      ("comm", Mpi_utils.get_typ "MPI_Comm", [])
    ]
  in
  TFun(ret, Some ps, false, [])

let generate_prototype t =
  let ftype = generate_function_type t in
  let name = function_name ^ "_" ^ (Mpi_utils.string_of_typ t) in
  name, ftype

let well_typed_call _ret _fct = function
  | [ sendbuf ; sendcount ; sendtype; recvbuf ; recvcount ; recvtype; comm ] ->
    let test =
      Cil.isIntegralType (Cil.typeOf sendcount) &&
      Cil.isIntegralType (Cil.typeOf recvcount) &&
      Cil_datatype.Typ.equal (Cil.typeOf sendtype) (Mpi_utils.get_typ "MPI_Datatype") &&
      Cil_datatype.Typ.equal (Cil.typeOf recvtype) (Mpi_utils.get_typ "MPI_Datatype") &&
      Cil_datatype.Typ.equal (Cil.typeOf comm) (Mpi_utils.get_typ "MPI_Comm")
    in
    let ts = Mpi_utils.exp_type_of_pointed sendbuf in
    let tr = Mpi_utils.exp_type_of_pointed recvbuf in
    begin
      match ts,tr with
      | Some typ_s, Some typ_r ->
        let bs = (Cil_datatype.Typ.equal typ_s (Mpi_utils.mpi_to_cil_typ sendtype)) in
        let br = (Cil_datatype.Typ.equal typ_r (Mpi_utils.mpi_to_cil_typ recvtype)) in
        bs && br && test
      | _ , _ -> false
    end
  | _ -> false

let key_from_call _ret _fct args =
  match args with
  | [ sendbuf ; _ ; _ ; _ ; _ ; _ ; _ ] ->
    begin
      match Mpi_utils.exp_type_of_pointed sendbuf with
      | None -> assert false
      | Some typ -> typ
    end
  | _ -> assert false

let retype_args _ args =
  match args with
  | [ sendbuf ; sendcount ; sendtype; recvbuf ; recvcount ; recvtype; comm ] ->
    [ Cil.stripCasts sendbuf ; sendcount ; sendtype;
      Cil.stripCasts recvbuf; recvcount; recvtype ; comm]
  | _ -> assert false

module M =
struct
  module Hashtbl = Cil_datatype.Typ.Hashtbl
  type override_key = typ

  let function_name = function_name
  let well_typed_call = well_typed_call
  let key_from_call = key_from_call
  let retype_args = retype_args
  let generate_prototype = generate_prototype
  let generate_spec = generate_spec
  let args_for_original _ = Extlib.id
end

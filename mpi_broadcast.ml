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

let function_name = "MPI_Bcast"

let protocol_for_intbcast f =
  let t1 = Mpi_utils.getFirst_get_type_protocol () in
  let t2 = Mpi_utils.integer_var (List.nth f.sformals 3) in
  let t3 = Mpi_utils.integer_var (List.nth f.sformals 1) in
  let t4 = Logic_const.tvar (Cil.cvar_to_lvar (List.nth f.sformals 0)) in
  let t4 = Mpi_utils.to_list t4 t3 in
  let p =
    Mpi_utils.papp "isforIntBroadcast" (t1 :: t2 :: t3 :: t4 :: []) []
  in
  Mpi_utils.make_pred p "protocol_for_intbcast"

let pred_message f =
  let t1 = Logic_const.tvar (Cil.cvar_to_lvar (Mpi_utils.get_var "protocol")) in
  let t1 = Mpi_utils.tapp "get_type" (t1 :: []) [] in
  let t1 = Logic_const.told t1 in
  let t1 = Mpi_utils.tapp "getFirst" (t1 :: []) [] in

  let t2 = Logic_const.tvar (Cil.cvar_to_lvar (List.nth f.sformals 0)) in
  let t3 = Mpi_utils.integer_var (List.nth f.sformals 1) in
  let t2 = Mpi_utils.to_list t2 t3 in

  let p = Mpi_utils.papp "predIntBroadcast" (t1 :: t2 :: []) [] in
  Normal, Mpi_utils.make_pred p "pred_message"

let continu_protocol f =
  let t3 = Logic_const.tvar (Cil.cvar_to_lvar (Mpi_utils.get_var "protocol")) in
  let t3 = Mpi_utils.tapp "get_type" (t3 :: []) [] in
  let t1 = Logic_const.told t3 in

  let var = Cil_const.make_logic_var_local "tmp" (t1.term_type) in
  let info =
    { l_var_info = var;
      l_labels = [];
      l_tparams = [];
      l_type = Some t1.term_type;
      l_profile = [];
      l_body = LBterm t1 }
  in

  let tmp =  Logic_const.term (Tapp (info, [], [])) t1.term_type in

  let t1 = Mpi_utils.tapp "getFirst" (tmp :: []) [] in
  let t2 = Mpi_utils.tapp "getNext" (tmp :: []) [] in

  let t5 = Logic_const.tvar (Cil.cvar_to_lvar (List.nth f.sformals 0)) in
  let t4 = Mpi_utils.integer_var (List.nth f.sformals 1) in
  let t4 = Mpi_utils.to_list t5 t4 in

  let p = Mpi_utils.papp "countiIntBroadcast" (t1 :: t2 :: t3 :: t4 :: []) [] in

  let pred = Logic_const.unamed p in
  let p = Plet (info, pred) in

  Normal, Mpi_utils.make_pred p "continu_protocol"

let same_array f =
  let t1 = Logic_const.tvar (Cil.cvar_to_lvar (List.nth f.sformals 0)) in
  let t2 = Logic_const.tinteger 0 in
  let t3 = Mpi_utils.integer_var (List.nth f.sformals 1) in
  let label = BuiltinLabel Pre :: BuiltinLabel Post :: [] in

  let p = Mpi_utils.papp "same_array" (t1 :: t1 :: t2 :: t3 :: []) label in
  Normal, Mpi_utils.make_pred p "same_array"

let generate_spec t _ f : Cil_types.funspec =
  let kf = Globals.Functions.find_by_name function_name in
  let spec = Annotations.funspec kf in
  let spec = Visitor.visitFramacFunspec (new Mpi_utils.visitor_beh t f.sformals) spec in

  if String.equal (Mpi_utils.cil_typ_to_mpi_string t) "mpi_mpi_int" then
    let requires = [protocol_for_intbcast f] in
    let ensures = [continu_protocol f] in
    let ensures = pred_message f :: ensures in
    let spec = Mpi_utils.update_spec spec Cil.default_behavior_name requires ensures in
    let ensures = [same_array f] in
    Mpi_utils.update_spec spec "type_root" [] ensures
  else spec

let generate_function_type t =
  let ret = Cil.intType in
  let ps =
    [
      ("buf" , Mpi_utils.ptr_of t, []) ;
      ("count", Cil.intType, []);
      ("datatype", Mpi_utils.get_type "MPI_Datatype", []);
      ("root", Cil.intType, []);
      ("comm", Mpi_utils.get_type "MPI_Comm", [])
    ]
  in
  TFun(ret, Some ps, false, [])

let generate_prototype t =
  let ftype = generate_function_type t in
  let name = function_name ^ "_" ^ (Mpi_utils.string_of_typ t) in
  name, ftype

let well_typed_call _ret _fct = function
  | [ buf ; count ; datatype; root; comm] ->
    let test =
      Cil.isIntegralType (Cil.typeOf count) &&
      Cil.isIntegralType (Cil.typeOf root) &&
      Cil_datatype.Typ.equal (Cil.typeOf datatype) (Mpi_utils.get_type "MPI_Datatype") &&
      Cil_datatype.Typ.equal (Cil.typeOf comm) (Mpi_utils.get_type "MPI_Comm")
    in
    begin
      match Mpi_utils.exp_type_of_pointed buf with
      | None -> false
      | Some typ ->
        (Cil_datatype.Typ.equal typ (Mpi_utils.mpi_to_cil_typ datatype)) && test
    end
  | _ -> false

let key_from_call _ret _fct args =
  match args with
  | [ buf ; _ ; _ ; _ ; _ ] ->
    begin
      match Mpi_utils.exp_type_of_pointed buf with
      | None -> assert false
      | Some typ -> typ
    end
  | _ -> assert false

let retype_args _ args =
  match args with
  | [ buf ; count ; datatype; root; comm] ->
    [ Cil.stripCasts buf ; count ; datatype; root; comm]
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

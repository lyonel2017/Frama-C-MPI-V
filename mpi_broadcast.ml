open Cil_types

let function_name = "MPI_Bcast"

let generate_spec t f _ : Cil_types.funspec =
  let kf = Globals.Functions.find_by_name function_name in
  let spec = Annotations.funspec kf in
  let spec = Visitor.visitFramacFunspec (new Mpi_utils.visitor_beh t f.sformals) spec in
  spec

let generate_function_type t =
  let ret = Cil.intType in
  let ps =
    [
      ("buf" , Mpi_utils.const_of(Mpi_utils.ptr_of t), []) ;
      ("count", Cil.intType, []);
      ("datatype", Mpi_utils.mpi_datatype (), []);
      ("root", Cil.intType, []);
      ("comm", Mpi_utils.mpi_comm (), [])
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
      Cil_datatype.Typ.equal (Cil.typeOf datatype) (Mpi_utils.mpi_datatype ()) &&
      Cil_datatype.Typ.equal (Cil.typeOf comm) (Mpi_utils.mpi_comm ())
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

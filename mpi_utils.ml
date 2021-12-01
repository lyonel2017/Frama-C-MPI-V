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

let string_of_typ_aux = function
  | TInt(IBool, _) -> "bool"
  | TInt(IChar, _) -> "char"
  | TInt(ISChar, _) -> "schar"
  | TInt(IUChar, _) -> "uchar"
  | TInt(IInt, _) -> "int"
  | TInt(IUInt, _) -> "uint"
  | TInt(IShort, _) -> "short"
  | TInt(IUShort, _) -> "ushort"
  | TInt(ILong, _) -> "long"
  | TInt(IULong, _) -> "ulong"
  | TInt(ILongLong, _) -> "llong"
  | TInt(IULongLong, _) -> "ullong"
  | TFloat(FFloat, _) -> "float"
  | TFloat(FDouble, _) -> "double"
  | TFloat(FLongDouble, _) -> "ldouble"
  | t -> MPI_V_options.Self.abort "unsupported type %a" Cil_printer.pp_typ t

let string_of_typ t = string_of_typ_aux (Cil.unrollType t)

let mpi_to_cil_typ datatype =
  match datatype.enode with
  | AddrOf (Var v ,_) when String.equal v.vname "mpi_mpi_int" ->
    Cil.intType
  | AddrOf (Var v ,_) when String.equal v.vname "mpi_mpi_float" ->
    Cil.floatType
  | AddrOf (Var v ,_) when String.equal v.vname "mpi_mpi_char" ->
    Cil.charType
  | _ ->  MPI_V_options.Self.abort "Unsupported MPI datatype %a" Cil_printer.pp_exp datatype

let cil_typ_to_mpi_string t =
  match t with
  | TInt(IInt,[]) -> "mpi_mpi_int"
  | TFloat(FFloat,[]) -> "mpi_mpi_float"
  | TInt(IChar,[]) -> "mpi_mpi_char"
  | _ -> MPI_V_options.Self.abort "Unsupported type %a" Cil_printer.pp_typ t

let get_type s =
    Globals.Types.find_type Logic_typing.Typedef s

let get_var s =
  match Globals.Syntactic_search.find_in_scope s Program  with
  | None -> MPI_V_options.Self.fatal "Varinfo of %s not found" s
  | Some v -> v

let get_l_info s =
  match Logic_env.find_all_logic_functions s with
  | h :: _ -> h
  | [] -> MPI_V_options.Self.fatal "Logic_info of %s not found" s

let ptr_of t = TPtr(t, [])
let const_of t = Cil.typeAddAttributes [Attr("const", [])] t

let exp_type_of_pointed buf =
  let no_cast = Cil.stripCasts buf in
  let no_cast_type = Cil.typeOf no_cast in
  if not (Cil.isPointerType no_cast_type) then
    match Cil.constFoldToInt buf with
    | Some t when Integer.(equal t (of_int 0)) ->
      let typ = Cil.typeOf_pointed (Cil.typeOf buf) in
      Some typ
    | _ -> None
  else
    let xt = Cil.unrollTypeDeep no_cast_type in
    let xt = Cil.type_remove_qualifier_attributes_deep xt in
    let typ = Cil.typeOf_pointed xt in
    Some typ

class visitor_datatype t = object(_)
  inherit Visitor.frama_c_copy (Project.current())

  method! vterm_node _ =
    let aux node =
      match node with
      | TAddrOf((TVar _, TNoOffset)) ->
        let v = Globals.Vars.find_from_astinfo (cil_typ_to_mpi_string t) VGlobal in
        let lv = Cil.cvar_to_lvar v in
        TAddrOf((TVar lv, TNoOffset))
      | _ -> node
    in
    Cil.DoChildrenPost aux
end

class visitor_convert t = object(_)
  inherit Visitor.frama_c_copy (Project.current())

  method! vterm _ =
    let f term =
      match term.term_node with
      | TCastE (TPtr(typ,[]),terl) when Cil.isCharType typ ->
        {term with term_type = (Ctype (ptr_of t));term_node = TCastE(ptr_of t,terl)}

      | TBinOp (PlusPI, term1, term2) ->
        begin
          match term1.term_node, term2.term_node, term.term_type with
          | TCastE (TPtr(_,[]), _) , Trange _, Ltype(info,_) ->
            {term with term_type = Ltype(info,[term1.term_type])}
          | _ -> term
        end

      | _ ->  term

    in
    Cil.DoChildrenPost f
end

class visitor_convert_ass t = object(_)
  inherit Visitor.frama_c_copy (Project.current())

  method! vterm _ =
    let f term =
      match term.term_node with
      | TCastE (TPtr(typ,[]),terl) when Cil.isCharType typ ->
        {term with term_type = (Ctype (ptr_of t));term_node = TCastE(ptr_of t,terl)}

      | TBinOp (IndexPI, term1, term2) ->
        begin
          match term1.term_node, term2.term_node, term.term_type with
          | TCastE (TPtr(_,[]), _) , Trange _, Ltype(info,_) ->
            {term with term_type = Ltype(info,[term1.term_type])}
          | _ -> term
        end

      | TLval (TMem term1,_) ->
        begin
        match term1.term_node, term.term_type, term1.term_type with
          | TBinOp _ , Ltype(info,_), Ltype(_,[Ctype(TPtr(t, []))])->
            {term with term_type = Ltype(info,[Ctype t])}
          | _ -> term
      end
      | _ -> term
    in
    Cil.DoChildrenPost f
end

class visitor_beh t formals = object(self)
  inherit Visitor.frama_c_refresh (Project.current ())

  val type_name = string_of_typ t

  method private filter_requires (lr: identified_predicate list) =
    let aux r =
      let name = r.ip_content.tp_statement.pred_name in
      match name with
      | [] -> true
      | h :: [] when String.equal h "danglingness_buf" ->
        false
      | h :: [] when String.equal h "initialization_buf" ->
        false
      | _ -> true
    in
    List.filter aux lr

  method private review_requires r =
    let name = r.ip_content.tp_statement.pred_name in
    match name with
    | [] -> r
    | h :: [] when String.equal h "danglingness_buf" ||
                   String.equal h "initialization_buf" ||
                   String.equal h "valid_buf" ->
      Visitor.visitFramacIdPredicate (new visitor_convert t) r
    | h :: [] when String.equal h "datatype" ->
      Visitor.visitFramacIdPredicate (new visitor_datatype t) r
    | _ -> r

  method private require_processing (l: identified_predicate list) =
    let l = List.map self#review_requires l in
    let l = self#filter_requires l in
    l

  method private assigns_processing a =
    let aux f =
      let term,deps = f in
      let term = Visitor.visitFramacIdTerm (new visitor_convert_ass t) term in
      (term,deps)
    in
    match a with
    | WritesAny -> a
    | Writes l -> Writes(List.map aux l)

  method! vterm _ =
    let f term =
      match term.term_node with
      | TLval(TVar lv, offset)  ->
        begin
          let f vi = String.equal lv.lv_name vi.vname in
          match List.find f formals with
          | vv ->
            let lv = Cil.cvar_to_lvar vv in
            {term with term_type = lv.lv_type; term_node = TLval(TVar lv, offset)}
          | exception _ -> term
        end
      | _ -> term
    in
    Cil.DoChildrenPost f

  method! vspec _ =
    let aux b =
      let b_requires = self#require_processing b.b_requires in
      let b_assigns = self#assigns_processing b.b_assigns in
      {b with  b_requires; b_assigns}
    in
    let f fspec =
      let spec_behavior = List.map aux fspec.spec_behavior in
      {fspec with spec_behavior}
    in
    Cil.DoChildrenPost f
end

let return_type l_i =
  match l_i.l_type with
  | Some t -> t
  | None ->
    MPI_V_options.Self.fatal "No return type for Logic_info %a" Cil_printer.pp_logic_info l_i

let tapp s p l =
  let l_i = get_l_info s in
  Logic_const.term (Tapp (l_i, l, p)) (return_type l_i)

let papp s p l =
  let l_i = get_l_info s in
  Papp (l_i, l, p)

let make_pred p name =
  let pred = {(Logic_const.unamed p) with pred_name = [name] } in
  Logic_const.new_predicate pred

let getFirst_get_type_protocol () =
  let t1 = Logic_const.tvar (Cil.cvar_to_lvar (get_var "protocol")) in
  let t4 = tapp "get_type" (t1 :: []) [] in
  tapp "getFirst" (t4 :: []) []

let to_list t1 t3 =
  let t2 = Logic_const.tinteger 0 in
  let t3 = Logic_const.tlogic_coerce t3 (Cil_types.Linteger) in
  tapp "to_list" (t1 :: t2 :: t3 :: []) [BuiltinLabel Here]

let integer_var v =
  let t = Logic_const.tvar (Cil.cvar_to_lvar v) in
  Logic_const.tlogic_coerce t (Cil_types.Linteger)

let reduce_protocol () =
  let t1 = Logic_const.tvar (Cil.cvar_to_lvar (get_var "protocol")) in
  let t2 = tapp "get_type" (t1 :: []) [] in
  let t2 = Logic_const.told t2 in
  let t2 = tapp "getNext" (t2 :: []) [] in

  papp "set_type" (t1 :: t2 :: []) []

let same_array var1 var2 =
  let t1 = Logic_const.tvar (Cil.cvar_to_lvar var1) in
  let t2 = Logic_const.tinteger 0 in
  let t3 = integer_var var2 in

  let var = Cil_const.make_logic_var_quant "k" (Cil_types.Linteger) in
  let tk =  Logic_const.tvar var in

  let pred1 = Logic_const.prel (Rle, t2, tk) in
  let pred2 = Logic_const.prel (Rlt, tk, t3) in

  let pred1 = Logic_const.pand (pred1, pred2) in

  let t1 = Logic_const.term (TBinOp (PlusPI, t1, tk)) (t1.term_type) in

  let typ = match t1.term_type with
    | Ctype typ -> Ctype (Cil.typeOf_pointed typ)
    | _ -> assert false
  in

  let t4 = Logic_const.term (TLval (TMem t1,TNoOffset)) typ in

  let tpre = Logic_const.tat(t4,BuiltinLabel Pre) in
  let tpost = Logic_const.tat(t4,BuiltinLabel Post) in

  let pred2 = Logic_const.prel (Req, tpre, tpost) in

  let pred = Logic_const.pimplies (pred1, pred2) in
  Pforall([var],pred)

let update_spec spec name requires ensures =
  let has_same_name b = b.b_name = name in
  let aux b =
    if has_same_name b then
      let b_requires = b.b_requires @ requires in
      let b_post_cond = ensures @ b.b_post_cond in
      {b with b_requires; b_post_cond}
    else b
  in
  let spec_behavior = List.map aux spec.spec_behavior in
  {spec with spec_behavior}

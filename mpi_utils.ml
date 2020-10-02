open Cil_types

let rec string_of_typ_aux = function
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

class visitor_beh t formals = object(self)
  inherit Visitor.frama_c_refresh (Project.current ())

  val type_name = "type_" ^ (string_of_typ t)

  method! vterm _ =
    let f term =
      match term.term_node with
      | TLval(TVar lv, _) when
          not(Cil_datatype.Logic_type.equal lv.lv_type term.term_type) ->
        {term with term_type = lv.lv_type}
      | _ -> term
    in
    Cil.DoChildrenPost f

  method private merge_assigns a1 a2 =
    match a1 with
    | WritesAny -> a2
    | Writes f1 ->
      begin
        match a2 with
        | WritesAny -> a1
        | Writes f2 -> Writes (f1@f2)
      end

  method private filter_requires (lr: identified_predicate list) =
    let aux r =
      let name = r.ip_content.tp_statement.pred_name in
      match name with
      | [] -> true
      | h :: [] ->
        let b =String.equal h "danglingness_buf" in
        not b
      | _ -> true
    in
    List.filter aux lr

  method! vspec _ =
    let is_type_behavior b = String.equal b.b_name type_name  in
    let f fspec =
      let type_behavior =
        try List.find is_type_behavior fspec.spec_behavior with
        | Not_found ->
          MPI_V_options.Self.abort "No behavior for type %a in " Cil_printer.pp_typ t
      in
      let default_behavior = List.find Cil.is_default_behavior fspec.spec_behavior in
      let type_require = self#filter_requires type_behavior.b_requires in
      let new_default_requires = default_behavior.b_requires @  type_require in
      let new_default_ensures = default_behavior.b_post_cond @ type_behavior.b_post_cond in
      let new_default_assigns =
        self#merge_assigns default_behavior.b_assigns type_behavior.b_assigns
      in
      let default_behavior = {default_behavior with
                              b_requires = new_default_requires;
                              b_post_cond = new_default_ensures;
                              b_assigns = new_default_assigns}
      in
      {fspec with spec_behavior = [default_behavior]}
    in
    Cil.DoChildrenPost f

  method! vlogic_var_use l =
    let f vi = String.equal l.lv_name vi.vname in
    match List.find f formals with
    | vv ->
      let l = Cil.cvar_to_lvar vv in
      Cil.ChangeTo l
    | exception _ -> Cil.JustCopy
end

let mpi_comm () =
  Globals.Types.find_type Logic_typing.Typedef "MPI_Comm"

let mpi_status () =
  Globals.Types.find_type Logic_typing.Typedef "MPI_Status"

let mpi_datatype () =
  Globals.Types.find_type Logic_typing.Typedef "MPI_Datatype"

let ptr_of t = TPtr(t, [])
let const_of t = Cil.typeAddAttributes [Attr("const", [])] t

let mpi_to_cil_typ datatype =
  match datatype.enode with
  | AddrOf (Var v ,_) when String.equal v.vname "mpi_mpi_int" ->
    Cil.intType
  | AddrOf (Var v ,_) when String.equal v.vname "mpi_mpi_char" ->
    Cil.charType
  | _ ->  MPI_V_options.Self.abort "Unknown MPI datatype %a" Cil_printer.pp_exp datatype

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

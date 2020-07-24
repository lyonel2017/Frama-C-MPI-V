val string_of_typ : Cil_types.typ -> string

class visitor_beh: Cil_types.typ -> Cil_types.varinfo list -> Visitor.generic_frama_c_visitor

val mpi_comm: unit -> Cil_types.typ

val mpi_status: unit -> Cil_types.typ

val mpi_datatype: unit -> Cil_types.typ

val ptr_of: Cil_types.typ -> Cil_types.typ

val const_of: Cil_types.typ -> Cil_types.typ

val mpi_to_cil_typ: Cil_types.exp -> Cil_types.typ

val exp_type_of_pointed: Cil_types.exp -> Cil_types.typ option

open Cil_types

let add_hypo () =
  if MPI_V_options.Numproc.is_set () then
    begin
      let n = MPI_V_options.Numproc.get () in
      let var = Globals.Syntactic_search.find_in_scope "__MPI_COMM_WORLD_size_ACSL" Program in
      let var = match var with
        | Some v -> v
        | None -> assert false
      in
      let term1 =  Logic_const.tvar (Cil.cvar_to_lvar var) in
      let term2 = Logic_const.tinteger n in
      let term2 = Logic_const.tcast term2 Cil.intType in
      let pred = Logic_const.prel (Req,term1,term2)  in
      let pred = (Normal,Logic_const.new_predicate pred) in
      let kf = Globals.Functions.find_by_name "MPI_Init" in
      Annotations.add_ensures MPI_V_options.emitter kf [pred]
  end

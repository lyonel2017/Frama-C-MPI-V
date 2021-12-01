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

let () =
  let add_mpi_v_lib () =
    let share = MPI_V_options.Self.Share.get_dir ~mode:`Must_exist "." in
    Kernel.CppExtraArgs.add
      (Format.asprintf " -I%a" Datatype.Filepath.pp_abs share);

    if Plugin.is_present "instantiate" then
      Dynamic.Parameter.Bool.on "-instantiate" ();
  in
  Cmdline.run_after_configuring_stage add_mpi_v_lib

let () =
  Instantiate.Transform.register (module Mpi_recv.M:Instantiate.Instantiator_builder.Generator_sig);
  Instantiate.Transform.register (module Mpi_ssend.M:Instantiate.Instantiator_builder.Generator_sig);
  Instantiate.Transform.register
    (module Mpi_broadcast.M:Instantiate.Instantiator_builder.Generator_sig);
  Instantiate.Transform.register
    (module Mpi_gather.M:Instantiate.Instantiator_builder.Generator_sig);
  Instantiate.Transform.register
    (module Mpi_allgather.M:Instantiate.Instantiator_builder.Generator_sig);
  Instantiate.Transform.register
    (module Mpi_scatter.M:Instantiate.Instantiator_builder.Generator_sig);
  Instantiate.Transform.register
    (module Mpi_reduce.M:Instantiate.Instantiator_builder.Generator_sig);
  Instantiate.Transform.register
    (module Mpi_allreduce.M:Instantiate.Instantiator_builder.Generator_sig)

let category = File.register_code_transformation_category "mpi-v"

let () =
  let perform _file =
    if MPI_V_options.Enabled.get () then
      Mpi_main.add_priority_condition ()
  in
  File.add_code_transformation_after_cleanup category perform

let run () =
  if MPI_V_options.Enabled.get () then
    begin
      File.pretty_ast ();
      Filecheck.check_ast "MPI-V"
    end

let () = Db.Main.extend run

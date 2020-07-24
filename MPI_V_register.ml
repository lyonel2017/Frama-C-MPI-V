let () =
  let add_mpi_v_lib () =
    let share = MPI_V_options.Self.Share.get_dir ~mode:`Must_exist "." in
    Kernel.CppExtraArgs.add
      (Format.asprintf " -I%a" Datatype.Filepath.pp_abs share);

    Kernel.Keep_unused_specified_functions.off ();
    let ppc, ppk = File.get_preprocessor_command () in
    let file = MPI_V_options.Self.Share.get_file ~mode:`Must_exist "mpi.h" in

    File.pre_register
      (File.NeedCPP
         (file,
          ppc
          ^ Format.asprintf " -I%a" Datatype.Filepath.pp_abs share,
          ppk));
    if Plugin.is_present "instantiate" then
      Dynamic.Parameter.Bool.on "-instantiate" ();
  in
  Cmdline.run_after_configuring_stage add_mpi_v_lib


let run () =
  if MPI_V_options.Enabled.get () then
    begin
      MPI_V_core.add_hypo ();
      File.pretty_ast ();
      Filecheck.check_ast "Rpp"
    end

let () =
  Instantiate.Transform.register (module Mpi_recv.M:Instantiate.Instantiator_builder.Generator_sig);
  Instantiate.Transform.register (module Mpi_ssend.M:Instantiate.Instantiator_builder.Generator_sig);
  Db.Main.extend run

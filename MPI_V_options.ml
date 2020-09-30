module Self = Plugin.Register(struct
    let name = "MPI-V"
    let shortname = "mpi-v"
    let help = "Verification of MPI program"
  end)

module Enabled = Self.False(struct
    let option_name = "-mpi-v"
    let help = "when on (off by default), verifies MPI program."
  end)

let emitter = Emitter.create "mpi-v" [Emitter.Funspec] ~correctness:[] ~tuning:[]

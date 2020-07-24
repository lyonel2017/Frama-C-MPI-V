module Self = Plugin.Register(struct
    let name = "MPI-V"
    let shortname = "mpi-v"
    let help = "Verification of MPI program"
  end)

module Enabled = Self.False(struct
    let option_name = "-mpi-v"
    let help = "when on (off by default), verifies MPI program."
  end)

module Numproc = Self.Int(struct
    let option_name = "-mpi-v-n"
    let default = 0
    let arg_name = "numproc"
    let help =
      "the number of assumed MPI process"
  end)

let emitter = Emitter.create "mpi-v" [Emitter.Funspec] ~correctness:[] ~tuning:[]

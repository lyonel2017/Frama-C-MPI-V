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

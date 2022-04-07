#  Frama-C-MPI-V

This is the *MPI-V (Message Passing Interface Verifier)* plug-in for *Frama-C*.
The tool allow to verify deadlock freedom, session fidelity and fonctional correcness
for distributed programming written in C using
the *Message Passing Interface* [MPI](https://www.mpi-forum.org/).
*MPI-V* is based on the concept of multiparty session types and inspired from
the idea proposed in [ParTypes](http://rss.di.fc.ul.pt/tools/partypes/#Downloads).

The tool support a small supset of the
[MPI v1.3](https://www.mpi-forum.org/docs/mpi-1.3/mpi-report-1.3-2008-05-30.pdf)
standard. Support function included :
* Synchronous point-to-point communication: `MPI_Ssend` and `MPI_Recv`
* Collective communication: `MPI_Bcast`, `MPI_Gather`, `MPI_Scatter`

## Installation

*MPI-V <!-- v0.0.0 -->* requires [Frama-C v24.0 (Chromium)](https://git.frama-c.com/pub/frama-c).
For more information see [Frama-C](http://frama-c.com).

For installation, run following commands in the *MPI-V* project directory
(assuming you have *Frama-C* in your `PATH`):

        make
        make install


## Usage

Assume we have following MPI program in a file named `code_mpi.c`.
```c
#include "mpi.h"

int main(int argc, char **argv){
	int data, my_rank, num_procs;

	MPI_Init(&argc, &argv);
	MPI_Comm_rank(MPI_COMM_WORLD, &my_rank);
	MPI_Comm_size(MPI_COMM_WORLD, &num_procs);

	if (my_rank == 0) {
		data = my_rank;
		MPI_Ssend(&data, 1, MPI_INT, 1, 1, MPI_COMM_WORLD);
	}
	else{
		if (my_rank == 1){
			MPI_Recv(&data, 1, MPI_INT, 0, 1, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
			//@ check data == 0;
		}
		/*@ ghost
			else {
				next();
			}
		*/
	}
	MPI_Finalize();
	return 0;
}
```
The MPI program performes a synchronous point-to-point communication
from processes with rank `0` to `1`. The size of the transfert data is `1` and of type `MPI_INT`.
The tag used for the communication is `1`.
Not action is performed by the processes with rank different form `0` and `1`.

This behaviour can be define by a protocol constant `the_protocol`
of type `protocol` (defined in `share/protocol.why`)
in a *Why3* file (we named it `the_protocol.why`):

```ml
module MPI_the_protocol

	use frama_c_wp.vlist.Vlist
	use protocol.MPI_Protocol
	use int.Int

	constant the_protocol : protocol =
           IntMessage 0 1 1 1 (fun l -> nth l 0 = 0)

end
```
The first parameter of constructor `IntMessage` specifies the source of the message,
the second parameter the destination, the third parameter the size of the send data,
the fourth parameter the message tag,
and the fifth parameter the property satified by the send data (the send data is
represented by a list).

We can also constraine the world size in a *Why3* file (we name it `size.why`).
For the program in `code_mpi.c` to be correct, it is required that the number of processes
is greater than 1. Using the `size_constrain`, we can specifies this constrain:

```ml
module MPI_size

	use int.Int

	predicate size_constrain (s: int) = s > 1

end
```
The protocol and the world size constraint is bind with *Frama-C* using two drivers
(called here `the_protocol.driver` and `size.driver`). More information about
*Frama-C/WP* drivers can be found in the [Frama-C/WP manual](https://frama-c.com/download/frama-c-wp-manual.pdf):

```
library mpi_size_constrain:

predicate "size_constrain" (integer) = "size_constrain";
why3.file += "size.why:MPI_size";
```

```
library the_protocol:

logic logic_protocol "the_protocol" = "the_protocol";
why3.file += "the_protocol.why:MPI_the_protocol";
```

The `ACSL` symboles `size_constrain` and `the_protocol` must be used in the driver for binding
respectively the world size and the protocol.

To run the example, following command can be used:

	frama-c-gui -mpi-v -wp-driver FRAMAC-SHARE-PATH/mpi-v/mpi.driver,the_protocol.driver,size.driver code_mpi.c

where `FRAMAC-SHARE-PATH` is the path returned by `frama-c -print-share-path`.

More examples can be found in the folder `test/`.

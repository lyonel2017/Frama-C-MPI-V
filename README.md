#  Frama-C-MPI-V

This is the *MPI-V (Message Passing Interface Verifier)* plug-in for *Frama-C*.
The plugin allow to verify deadlock freedom session fidelity and fonctional correcness in the case
of distributed programming written in C using the *Message Passing Interface* [MPI](https://www.mpi-forum.org/).
*MPI-V* is based on the concept of session types and inspired form the approach proposed in
[ParTypes](http://rss.di.fc.ul.pt/tools/partypes/#Downloads).

The tool support a small supset of the
[MPI v1.3](https://www.mpi-forum.org/docs/mpi-1.3/mpi-report-1.3-2008-05-30.pdf)
standard. Support function included :
* Synchronous point-to-point communication: `MPI_Ssend` and `MPI_Recv`
* Collective communication: `MPI_Bcast`, `MPI_Gather`, `MPI_Scatter`

## Installation

*MPI-V v0.0.0* requires [Frama-C v23.1 (Vanadium)](https://git.frama-c.com/pub/frama-c). For more information see [Frama-C](http://frama-c.com).

For installation, run following commands in the *MPI-V* directory:

        make
        make install


## Usage

Assume you have a MPI program in a file named `code_mpi.c`.
```c
#include "mpi.h"

int main(int argc, char **argv){
	int data = 0;
	int my_rank = 0;
	int num_procs = 0;

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
			//@ assert data == 0;
		}
		/*@ ghost
			else {
				toskip();
			}
		*/
	}
	MPI_Finalize();
	return 0;
}
```
You define in a *Why3* file (we named it `the_protocol.why`) a protocol following
the type `protocol` defined in `share/protocol.why`:

```ml
module MPI_the_protocol

	use protocol.MPI_Protocol

	constant the_protocol : protocol =
           IntMessage 0 1 1 1 (fun l -> nth l 0 = 0)

end
```

You can also constraine the world size in a *Why3* file (we name it `size.why`):

```ml
module MPI_size

	use int.Int

	predicate size_constrain (s: int) = s > 1

end
```
Finaly you bind your protocol and your world size constraint with *Frama-C* using two drivers
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

Be careful to use the `ACSL` symboles `size_constrain` and `the_protocol` in the driver for binding
respectively the world size and the protocol.

To run the example use following command :

	frama-c-gui -mpi-v -wp-driver FRAMAC-SHARE-PATH/mpi-v/mpi.driver,the_protocol.driver,size.driver code_mpi.c

where `FRAMAC-SHARE-PATH` is the path returned by `frama-c -print-share-path`.

More examples can be found in the folder `test/`.

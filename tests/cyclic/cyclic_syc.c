#include <mpi.h>

//frama-c-gui -mpi-v -wp-driver ../../share/mpi.driver,the_protocol.driver,size.driver cyclic_syc.c

int main(int argc,char** argv) {
  int rank, procs, left, right, iter, sendbuf, recvbuf;

  MPI_Init( &argc, &argv );
  MPI_Comm_rank( MPI_COMM_WORLD, &rank );
  MPI_Comm_size( MPI_COMM_WORLD, &procs );

  left = rank == 0 ? procs - 1 : rank -1;
  right = rank == procs - 1 ?  0 : rank + 1;

  sendbuf = rank;

  /*@ loop invariant 0 <= iter <= procs;
    @ loop invariant getLeft(get_type(protocol)) ==
    @   split_right(\at(get_type(protocol),LoopEntry),iter);
    @ loop invariant isSkip(getRight(get_type(protocol)));
    @ loop invariant iter > 0 ==> sendbuf == recvbuf;
    @ loop invariant rank >= iter ==> sendbuf == rank - iter;
    @ loop invariant rank < iter ==> sendbuf == (procs - iter) + rank;
    @ loop assigns protocol,recvbuf,sendbuf,iter;
    @ loop variant procs-iter;
    @*/
  for (iter = 0; iter < procs; iter++) {
    /*@ ghost
      unroll();
      assoc();
      @*/
    if (rank == 0) {
      /*@ ghost
	unroll();
	assoc();
	@*/
      // message 0 1
      MPI_Ssend(&sendbuf, 1, MPI_INT, right, 0, MPI_COMM_WORLD);
      /*@ ghost
	split(procs - 1);
	assoc();
	fsimpl();
	unroll();
	assoc();*/
      MPI_Recv(&recvbuf, 1, MPI_INT, left,  0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);

      /*@ ghost next();*/
      sendbuf = recvbuf;
    }
    else{
      /*@ ghost
	split(rank-1);
	assoc();
	fsimpl();
	unroll();
	assoc();*/
      MPI_Recv(&recvbuf, 1, MPI_INT, left,  0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);

      /*@ ghost
	unroll();
	assoc();
	@*/
      MPI_Ssend(&sendbuf, 1, MPI_INT, right, 0, MPI_COMM_WORLD);
      /*@ ghost fsimpl();*/

      sendbuf = recvbuf;

    }
  }
  /*@ ghost next(); */
  /*@ check recvbuf == rank;*/
  MPI_Finalize();
  return 0;
}

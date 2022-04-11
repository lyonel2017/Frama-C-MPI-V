#include <mpi.h>

//frama-c-gui -mpi-v -wp-driver ../../../share/mpi.driver,the_protocol.driver,size.driver shift.c

int main(int argc,char** argv) {
  int nprocs; // number of processes
  int rank; // my PID
  int x,y;
  MPI_Init(&argc, &argv );
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
  
  x = rank;
  
  if (rank < nprocs - 1){
    /*@ ghost
      split((nprocs - 2) - rank);
      assoc();
      fsimpl();
      unroll();
      assoc();*/

    // send buffer, count, datatype, destination, tag (use 0), communicator
    MPI_Ssend(&x, 1, MPI_INT, rank+1, 0, MPI_COMM_WORLD);
  }

  if (rank > 0) {
  /*@ ghost
    unroll();
    assoc();*/

    MPI_Recv(&y, 1, MPI_INT, rank-1, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    /*@ check(y == rank - 1);*/
  }
  /*@ ghost fsimpl();*/

  MPI_Finalize();
}

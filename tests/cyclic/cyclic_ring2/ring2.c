#include <mpi.h>

//frama-c-gui -mpi-v -wp-driver ../../../share/mpi.driver,the_protocol.driver,size.driver ring2.c

// works for synchronous or asynchronous communication
int main(int argc,char** argv) {
  int nprocs; // number of processes
  int left,right,rank; // my PID
  int x,y;
  MPI_Init(&argc, &argv);
  MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);

  left = rank == 0 ? nprocs - 1 : rank -1;
  right = rank == nprocs - 1 ?  0 : rank + 1;

  x = rank;
  if (rank%2 == 0) {
    /* ghost
      split(rank/2);
      assoc();
      fsimpl();
      unroll();
      assoc();*/
    //MPI_Ssend(&x, 1, MPI_INT, right, 0, MPI_COMM_WORLD);
    /* ghost  fsimpl(); */

  /*@ ghost
      split(rank/2);
      assoc();
      fsimpl();
      unroll();
      assoc();*/
    MPI_Recv(&y, 1, MPI_INT, left, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    /*@ ghost fsimpl();*/
  } else {
    /* ghost
      split(rank/2);
      assoc();
      fsimpl();
      unroll();
      assoc();*/
    //MPI_Recv(&y, 1, MPI_INT, left, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    /* ghost fsimpl();*/

  /*@ ghost
      split(rank/2);
      assoc();
      fsimpl();
      unroll();
      assoc();*/
    MPI_Ssend(&x, 1, MPI_INT, right, 0, MPI_COMM_WORLD);
    /*@ ghost fsimpl();*/
  }
  /* check y == (rank + nprocs - 1)%nprocs;*/
  MPI_Finalize();
}

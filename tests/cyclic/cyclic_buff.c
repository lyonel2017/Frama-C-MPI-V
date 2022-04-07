#include <mpi.h>

//TODO

int main(int argc,char** argv) {
  int rank, procs, left, right, iter, data, sendbuf, recvbuf;

  MPI_Init( &argc, &argv );
  MPI_Comm_rank( MPI_COMM_WORLD, &rank );
  MPI_Comm_size( MPI_COMM_WORLD, &procs );

  left = rank == 0 ? procs - 1 : rank -1;
  right = rank == procs - 1 ?  0 : rank + 1;

  sendbuf = rank;
  for (iter = 0; iter < procs; iter++) {
    MPI_BSend(sendbuf, 1, MPI_INT, right, 0, MPI_COMM_WORLD);
    MPI_Recv(recvbuf, 1, MPI_INT, left,  0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    sendbuf = recvbuf;
   }
  }
  /*@ check recvbuf == rank;*/
  MPI_Finalize();
  return 0;
}

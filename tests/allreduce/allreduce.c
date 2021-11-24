#include "mpi.h"
#include "stdio.h"

//frama-c-gui -mpi-v -wp-driver ../../share/mpi.driver,the_protocol.driver,size.driver allreduce.c

int main(int argc, char **argv) {
  int my_rank = 0, num_procs = 0;
  int sum[2];

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &my_rank);
  MPI_Comm_size(MPI_COMM_WORLD, &num_procs);

  int data[2];
  data[0] = my_rank * num_procs * 2;
  data[1] = my_rank * num_procs * 2 + 1;

  MPI_Allreduce(data, sum, 2, MPI_INT, MPI_SUM, MPI_COMM_WORLD);


  // printf("my rank: %i, sum_1: %i, sum_2: %i\n", my_rank, sum[0], sum[1]);

  MPI_Finalize();
  // assert \false;
}

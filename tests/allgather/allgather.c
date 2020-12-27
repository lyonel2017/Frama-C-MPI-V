#include "mpi.h" 
#include "stdio.h"

int main(int argc, char **argv) {
  int sum = 0, my_rank = 0, num_procs = 0;
  // assume a max of 100 processes
  int res[100]; 

  MPI_Init(&argc, &argv); 
  MPI_Comm_rank(MPI_COMM_WORLD, &my_rank);
  MPI_Comm_size(MPI_COMM_WORLD, &num_procs);

  
  /*@ loop invariant 0 <= i <= num_procs;
    @ loop assigns res[0 .. num_procs-1],i; 
    @ loop variant num_procs - i;
    @*/
  for (int i = 0; i < num_procs; i++) {
    res[i] = 0; 
  }

  //@ assert num_procs <= 100; 

  MPI_Allgather(&my_rank, 1, MPI_INT, res, 1, MPI_INT, MPI_COMM_WORLD);

  /*@ loop invariant 0 <= i <= num_procs; 
    @ loop assigns sum,i;
    @ loop variant num_procs - i; 
    @*/
  for (int i = 0; i < num_procs; i++) {
    sum += res[i]; 
  }
  // printf("my rank: %i, sum: %i\n", my_rank, sum);

  MPI_Finalize(); 
}
#include <stdio.h>
#include "mpi.h"


int main(int argc, char** argv) {
    // Initialize the MPI environment
    MPI_Init(NULL, NULL);

    // Get the number of processes
    int world_size;
    world_size = 0;
    MPI_Comm_size(MPI_COMM_WORLD, &world_size);

    // Get the rank of the process
    int world_rank = 0;
    MPI_Comm_rank(MPI_COMM_WORLD, &world_rank);

    // Print off a hello world message
    printf("Hello world from rank %d out of %d processes\n", world_rank, world_size);

    if(world_rank == 0){
      printf("I am the chef %d\n", world_rank);
    }
    else{
      printf("I am slave %d \n", world_rank);
    }

    // Finalize the MPI environment.
    MPI_Finalize();
}

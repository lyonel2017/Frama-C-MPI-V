#include "mpi.h"
#include <stdio.h>

//frama-c-gui -mpi-v -wp-driver ../../share/mpi.driver,the_protocol.driver,size.driver reduce_int.c

int main(int argc, char* argv){
    int numtasks, rank;

    MPI_Init(&argc,&argv);
    MPI_Comm_size(MPI_COMM_WORLD, &numtasks);
    MPI_Comm_rank(MPI_COMM_WORLD, &rank);

    int local = 1;
    int global = 0;


    MPI_Reduce(&local, &global, 1, MPI_INT, MPI_SUM, 0, MPI_COMM_WORLD);

    if (rank == 0) {
        // printf("sum: %i\n", global);
    }
    MPI_Finalize();
}

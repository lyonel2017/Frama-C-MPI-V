#include "mpi.h"
#include <stdio.h>

int main(argc,argv) int argc; char *argv[];
{
    int numtasks, rank;

    MPI_Init(&argc,&argv);
    MPI_Comm_size(MPI_COMM_WORLD, &numtasks);
    MPI_Comm_rank(MPI_COMM_WORLD, &rank);

    float local = 1.0f; 
    float global = 0.0f; 


    MPI_Reduce(&local, &global, 1, MPI_FLOAT, MPI_SUM, 0, MPI_COMM_WORLD);

    if (rank == 0) {
        // printf("sum: %f\n", global); 
    } 
    MPI_Finalize();
}
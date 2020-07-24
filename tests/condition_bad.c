#include <stdio.h>
#include "mpi.h"

int main(int argc, char **argv)
{
    int data;
    int my_rank, num_procs;
    int condition1;
    int condition2;

    /* Initialize the infrastructure necessary for communication */
    MPI_Init(&argc, &argv);

    /* Identify this process */
    MPI_Comm_rank(MPI_COMM_WORLD, &my_rank);

    /* Find out how many total processes are active */
    MPI_Comm_size(MPI_COMM_WORLD, &num_procs);


    /* Until this point, all programs have been doing exactly the same.
       Here, we check the rank to distinguish the roles of the programs */
    if (my_rank < 5) {

      if(condition1){
	data = my_rank;
        /* Send messages to other processes with my_rank + 5*/
	MPI_Send(&data, sizeof(data), MPI_INT, my_rank + 5, 0, MPI_COMM_WORLD);
      }

    } else{
      if (my_rank < 10){

	  /* Receive message from process my_rank-5 */
	  MPI_Recv(buf, sizeof(data), MPI_INT, my_rank-5, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      }
    }

    /* Tear down the communication infrastructure */
    MPI_Finalize();
    return 0;
}

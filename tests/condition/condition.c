#include "mpi.h"

int main(int argc, char **argv)
{
  int data = 0;
  int my_rank = 0, num_procs = 0;
  /* Initialize the infrastructure necessary for communication */
  MPI_Init(&argc, &argv);

  /* Identify this process */
  MPI_Comm_rank(MPI_COMM_WORLD, &my_rank);

  /* Find out how many total processes are active */
  MPI_Comm_size(MPI_COMM_WORLD, &num_procs);

  /* Until this point, all programs have been doing exactly the same.
     Here, we check the rank to distinguish the roles of the programs */
  if (my_rank < 5) {

    data = my_rank;
    /* Send messages to other processes with my_rank + 5*/

    /* assert 0 <=  __MPI_COMM_WORLD_rank_ACSL < 5;*/
    /* assert 5 <=  my_rank + 5 < 10;*/
    MPI_Ssend(&data, 1, MPI_INT, my_rank + 5, 0, MPI_COMM_WORLD);
  } else{
    if (my_rank < 10){

      /* Receive message from process my_rank-5 */
      /* assert 5 <=  __MPI_COMM_WORLD_rank_ACSL < 10;*/
      /* assert 0 <= my_rank-5 < 5;*/
      MPI_Recv(&data, 1, MPI_INT, my_rank-5, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    }
  }

  /* Tear down the communication infrastructure */
  MPI_Finalize();
  return 0;
}

#include "mpi.h"

//frama-c-gui -mpi-v -wp-driver ../../share/mpi.driver,the_protocol.driver,size.driver broadcast.c

int main(int argc, char **argv){
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
  if (my_rank == 0) {

    data = my_rank;
    /* Send messages to processes 1*/
    MPI_Bcast(&data, 1, MPI_INT, 0, MPI_COMM_WORLD);
    //@ ghost toskip();
  } else{

    /* Receive message from process 0 */
    MPI_Bcast(&data, 1, MPI_INT, 0, MPI_COMM_WORLD);
    //@ ghost toskip();
  }

  /* Tear down the communication infrastructure */
  MPI_Finalize();
  return 0;
}

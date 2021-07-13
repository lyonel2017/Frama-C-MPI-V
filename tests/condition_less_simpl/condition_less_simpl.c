#include "mpi.h"

//frama-c-gui -mpi-v -wp-driver ../../share/mpi.driver,the_protocol.driver,size.driver condition_less_simpl.c

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

    //@ ghost simpl();

    /* Send messages to processes 1*/
    MPI_Ssend(&data, 1, MPI_INT, 1, 1, MPI_COMM_WORLD);

    //@ ghost simpl();

  } else{
    if (my_rank == 1){

      //@ ghost simpl();

      /* Receive message from process 0 */
      MPI_Recv(&data, 1, MPI_INT, 0, 1, MPI_COMM_WORLD, MPI_STATUS_IGNORE);

      //@ ghost simpl();
    }

    /*@ ghost
    else {
      simpl();
      toskip();
      simpl();
    }
    @*/

  }
  /* Tear down the communication infrastructure */
  MPI_Finalize();
  return 0;
}

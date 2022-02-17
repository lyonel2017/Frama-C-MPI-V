#include "mpi.h"

//frama-c-gui -mpi-v -wp-driver ../../share/mpi.driver,the_protocol.driver,size.driver condition.c

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
  if (my_rank < 10) {

    data = my_rank;
    /*@ ghost
       split(my_rank);
       assoc();
       fsimpl();
       unroll();
       assoc();
    @*/

    /* Send messages to other processes with my_rank + 5*/
    MPI_Ssend(&data, 1, MPI_INT, my_rank + 10, 1, MPI_COMM_WORLD);

    /*@ ghost fsimpl();
      @*/

  } else{
    if (my_rank < 20){

    /*@ ghost
         split(my_rank-10);
         assoc();
         fsimpl();
         unroll();
         assoc();
    @*/

      /* Receive message from process my_rank-10 */
      MPI_Recv(&data, 1, MPI_INT, my_rank-10, 1, MPI_COMM_WORLD, MPI_STATUS_IGNORE);

    /*@ ghost  fsimpl();
      @*/

    }
    /*@ ghost
    else {
         fsimpl();
    }
  @*/
  }

  /* Tear down the communication infrastructure */
  MPI_Finalize();

  return 0;
}

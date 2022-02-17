#include "mpi.h"

//frama-c-gui -mpi-v -wp-driver ../../share/mpi.driver,the_protocol.driver,size.driver loop_simpl.c

int main(int argc, char **argv){
  int buf = 0;
  int my_rank, num_procs;

  /* Initialize the infrastructure necessary for communication */
  MPI_Init(&argc, &argv);

  /* Identify this process */
  MPI_Comm_rank(MPI_COMM_WORLD, &my_rank);

  /* Find out how many total processes are active */
  MPI_Comm_size(MPI_COMM_WORLD, &num_procs);

  /* Until this point, all programs have been doing exactly the same.
     Here, we check the rank to distinguish the roles of the programs */
  if (my_rank == 0) {
    int count = 0;
    /* Send messages to all other processes */
    /*@ loop invariant 0 <= count <= 10;
      @ loop invariant getFirst(get_type(protocol)) ==
      @    split_right(getFirst(\at(get_type(protocol),LoopEntry)),count);
      @ loop invariant getNext(get_type(protocol)) ==
      @    getNext(\at(get_type(protocol),LoopEntry));
      @ loop assigns count, protocol;
      @ loop variant 9 - count;*/
    while (count <= 9) {

      //@ ghost unroll();
      //@ ghost assoc();

      MPI_Ssend(&buf, 1, MPI_INT, 1,0, MPI_COMM_WORLD);
      count++;
    }

    //@ ghost next();

  } else {
    if(my_rank == 1){
      int count = 0;
      /* Receive messages from all other process */
      /*@ loop invariant 0 <= count <= 10;
	@ loop invariant getFirst(get_type(protocol)) ==
	@    split_right (getFirst(\at(get_type(protocol),LoopEntry)),count);
	@ loop invariant getNext(get_type(protocol)) ==
	@    getNext(\at(get_type(protocol),LoopEntry));
	@ loop assigns count, protocol,buf;
	@ loop variant 9 - count;*/
      while (count <= 9){
	//@ ghost unroll();
	//@ ghost assoc();

	MPI_Recv(&buf, 1, MPI_INT, 0,0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
	count++;
      }

      //@ ghost next();
    }

    /*@ghost
    else {
         fsimpl();
    }
    @*/
  }
  /* Tear down the communication infrastructure */
  MPI_Finalize();
  return 0;
}

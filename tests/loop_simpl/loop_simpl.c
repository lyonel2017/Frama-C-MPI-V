#include "mpi.h"

int main(int argc, char **argv){
  char buf[2] = {'O','k'};
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
      @  getNext(split (getFirst(\at(get_type(protocol),LoopEntry)),count));
      @ loop invariant getNext(get_type(protocol)) ==
      @    getNext(\at(get_type(protocol),LoopEntry));
      @ loop assigns count, protocol;
      @ loop variant 9 - count;*/
    while (count <= 9) {

      /*ghost code*/
      unroll();
      assoc();
      /*ghost code*/

      MPI_Ssend(buf, sizeof(buf), MPI_CHAR, 1,0, MPI_COMM_WORLD);
      count++;
    }

    /*ghost code*/
    toskip();
    /*ghost code*/

  } else {
    if(my_rank == 1){
      int count = 0;
      /* Receive messages from all other process */
      /*@ loop invariant 0 <= count <= 10;
	@ loop invariant getFirst(get_type(protocol)) ==
	@  getNext(split (getFirst(\at(get_type(protocol),LoopEntry)),count));
	@ loop invariant getNext(get_type(protocol)) ==
	@    getNext(\at(get_type(protocol),LoopEntry));
	@ loop assigns count, protocol,buf[0..1];
	@ loop variant 9 - count;*/
      while (count <= 9){
      /*ghost code*/
      unroll();
      assoc();
      /*ghost code*/

	MPI_Recv(buf, sizeof(buf), MPI_CHAR, 0,0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
	count++;
      }

      /*ghost code*/
      toskip();
      /*ghost code*/
    }

    /*ghost code*/
    else {
      int i = 0;
      /*@ loop invariant 0 <= i <= 10;
	@ loop invariant getFirst(get_type(protocol)) ==
	@  getNext(split (getFirst(\at(get_type(protocol),LoopEntry)),i));
	@ loop invariant getNext(get_type(protocol)) ==
	@    getNext(\at(get_type(protocol),LoopEntry));
	@ loop assigns protocol,i;
	@ loop variant 9 -i;
      */
      while (i <= 9){
	unroll();
	assoc();
	toskip();
	i++;
      }
      toskip();
      /*ghost code*/

    }
  }
  /* Tear down the communication infrastructure */
  MPI_Finalize();
  return 0;
}

#include "mpi.h"

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
  l1:;
    /*ghost code*/
    int i = 0;
    /*@ loop invariant 0 <= i <= my_rank;
      @ loop invariant getFirst(get_type(protocol)) ==
      @  getNext(split (getFirst(\at(get_type(protocol),l1)),i));
      @ loop invariant getNext(get_type(protocol)) ==
      @    getNext(\at(get_type(protocol),l1));
      @ loop assigns protocol,i;
      @ loop variant my_rank -i;
    */
    while (i < my_rank){
      unroll();
      assoc();
      toskip();
      i++;
    }

    unroll();
    assoc();
    /*ghost code*/

    /* Send messages to other processes with my_rank + 5*/
    MPI_Ssend(&data, 1, MPI_INT, my_rank + 10, 1, MPI_COMM_WORLD);

    /*ghost code*/
    i++;
    /*@ loop invariant my_rank + 1 <= i <= 10;
      @ loop invariant getFirst(get_type(protocol)) ==
      @  getNext(split (getFirst(\at(get_type(protocol),l1)),i));
      @ loop invariant getNext(get_type(protocol)) ==
      @    getNext(\at(get_type(protocol),l1));
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



  } else{
    if (my_rank < 20){

    l2:;
      /*ghost code*/
      int i = 0;
      /*@ loop invariant 0 <= i <= my_rank-10;
	@ loop invariant getFirst(get_type(protocol)) ==
	@  getNext(split (getFirst(\at(get_type(protocol),l2)),i));
	@ loop invariant getNext(get_type(protocol)) ==
	@    getNext(\at(get_type(protocol),l2));
	@ loop assigns protocol,i;
	@ loop variant my_rank-10 -i;
      */
      while (i < (my_rank-10)){
	unroll();
	assoc();
	toskip();
	i++;
      }

      unroll();
      assoc();
      /*ghost code*/


      /* Receive message from process my_rank-5 */
      MPI_Recv(&data, 1, MPI_INT, my_rank-10, 1, MPI_COMM_WORLD, MPI_STATUS_IGNORE);

      /*ghost code*/
      i++;
      /*@ loop invariant my_rank + 1 -10 <= i <= 10;
	@ loop invariant getFirst(get_type(protocol)) ==
	@  getNext(split (getFirst(\at(get_type(protocol),l2)),i));
	@ loop invariant getNext(get_type(protocol)) ==
	@    getNext(\at(get_type(protocol),l2));
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

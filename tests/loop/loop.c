#include "mpi.h"

//frama-c-gui -mpi-v -wp-driver ../../share/mpi.driver,the_protocol.driver,size.driver loop.c


int main(int argc, char **argv)
{
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
        int other_rank;
        /* Send messages to all other processes */
	/*@ loop invariant 1 <= other_rank <= num_procs;
	  @ loop invariant getFirst(get_type(protocol)) ==
	  @   getNext(split (getFirst(\at(get_type(protocol),LoopEntry)),other_rank));
	  @ loop invariant getNext(get_type(protocol)) ==
	  @   getNext(\at(get_type(protocol),LoopEntry));
	  @ loop assigns other_rank, protocol;
	  @ loop variant num_procs - other_rank;*/
        for (other_rank = 1; other_rank < num_procs; other_rank++){
	  //@ ghost unroll();
	  //@ ghost assoc();
	  MPI_Ssend(&buf, 1, MPI_INT, other_rank,0, MPI_COMM_WORLD);
        }
	//@ ghost toskip();
        /* Receive messages from all other process */
	/*@ loop invariant 1 <= other_rank <= num_procs;
	  @ loop invariant getFirst(get_type(protocol)) ==
	  @   getNext(split (getFirst(\at(get_type(protocol),LoopEntry)),other_rank));
	  @ loop invariant getNext(get_type(protocol)) ==
	  @   getNext(\at(get_type(protocol),LoopEntry));
	  @ loop assigns other_rank, protocol,buf;
	  @ loop variant num_procs - other_rank;*/
	for (other_rank = 1; other_rank < num_procs; other_rank++){
	  //@ ghost unroll();
	  //@ ghost assoc();
	  MPI_Recv(&buf, 1, MPI_INT, other_rank,0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
        }
	//@ ghost toskip();
    } else {

    /*@ ghost
  l1:;
    int i = 1;
    /@ loop invariant 1 <= i <= my_rank;
      @ loop invariant getFirst(get_type(protocol)) ==
      @  getNext(split (getFirst(\at(get_type(protocol),l1)),i));
      @ loop invariant getNext(get_type(protocol)) ==
      @    getNext(\at(get_type(protocol),l1));
      @ loop assigns protocol,i;
      @ loop variant my_rank -i;
      @/
    while (i < my_rank){
      unroll();
      assoc();
      toskip();
      i++;
    }

    unroll();
    assoc();
    @*/

        /* Receive message from process #0 */
        MPI_Recv(&buf, 1, MPI_INT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);

    /*@ ghost
    i++;
     /@ loop invariant my_rank + 1 <= i <= num_procs;
      @ loop invariant getFirst(get_type(protocol)) ==
      @    getNext(split (getFirst(\at(get_type(protocol),l1)),i));
      @ loop invariant getNext(get_type(protocol)) ==
      @    getNext(\at(get_type(protocol),l1));
      @ loop assigns protocol,i;
      @ loop variant num_procs -i;
      @/
    while (i < num_procs){
      unroll();
      assoc();
      toskip();
      i++;
    }
    toskip();
    @*/

    /*@ assert \at(get_type(protocol),Here) == getNext(\at(get_type(protocol),l1));*/

    /*@ ghost
  l2:;
     i = 1;
     /@ loop invariant 1 <= i <= my_rank;
      @ loop invariant getFirst(get_type(protocol)) ==
      @  getNext(split (getFirst(\at(get_type(protocol),l2)),i));
      @ loop invariant getNext(get_type(protocol)) ==
      @    getNext(\at(get_type(protocol),l2));
      @ loop assigns protocol,i;
      @ loop variant my_rank -i;
      @/
    while (i < my_rank){
      unroll();
      assoc();
      toskip();
      i++;
    }

    unroll();
    assoc();
    @*/
        buf = buf + 1;
        /* Send message to process #0 */
        MPI_Ssend(&buf, 1, MPI_INT, 0,0, MPI_COMM_WORLD);

    /*@ ghost
    i++;
     /@ loop invariant my_rank + 1 <= i <= num_procs;
      @ loop invariant getFirst(get_type(protocol)) ==
      @    getNext(split (getFirst(\at(get_type(protocol),l2)),i));
      @ loop invariant getNext(get_type(protocol)) ==
      @    getNext(\at(get_type(protocol),l2));
      @ loop assigns protocol,i;
      @ loop variant num_procs -i;
      @/
    while (i < num_procs){
      unroll();
      assoc();
      toskip();
      i++;
    }
    toskip();
    @*/

    }
    /* Tear down the communication infrastructure */
    MPI_Finalize();
    return 0;
}

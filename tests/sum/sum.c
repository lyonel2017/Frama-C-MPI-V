#include "mpi.h"
#include <stdio.h>
#include <stdlib.h>

#define MAX_LENGTH 1000

// without fixed amount of procs needs about 100 seconds to be proven
int main(int argc, char **argv){
  int my_rank = 0, num_procs = 0;
  int data[MAX_LENGTH];

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &my_rank);
  MPI_Comm_size(MPI_COMM_WORLD, &num_procs);

  int offset = MAX_LENGTH / num_procs;
  int length = num_procs * offset;

  if (my_rank == 0) {
    // initialize array, size is fixed to 1000 elements
    // printf("array: ");
    /*@
      @ loop invariant 0 <= i <= MAX_LENGTH;
      @ loop assigns data[0 .. (MAX_LENGTH-1)], i;
      @ loop variant MAX_LENGTH - i;
      @*/
    for (int i = 0; i < MAX_LENGTH; i++) {
      data[i] = (i * 17 * 43) % 7;
      // printf("%i ", data[i]);
    }
    // printf("\n");
    // distribute array to other processes by mpi_ssend
    int i = 1;
    /*@ loop invariant 1 <= i <= num_procs;
      @ loop invariant getFirst(get_type(protocol)) ==
      @   getNext(split (getFirst(\at(get_type(protocol),LoopEntry)),i));
      @ loop invariant getNext(get_type(protocol)) ==
      @   getNext(\at(get_type(protocol),LoopEntry));
      @ // loop invariant \forall integer j; 0 <= j < i ==> MAX_LENGTH >= (j + 1) * offset - 1;
      @ loop assigns protocol, i;
      @ loop variant num_procs - i;
      @ */
    while (i < num_procs) {
      /*@ ghost
        unroll();
        assoc();
      */
      MPI_Ssend(&data[i*offset], offset, MPI_INT, i, 1, MPI_COMM_WORLD);
      i++;
    }
    //@ ghost toskip();

    // sum up the part of array belonging to process 0
    int sum = 0;
    /*@
      @ loop invariant 0 <= i <= offset;
      @ loop assigns i, sum;
      @ loop variant offset - i;
      @*/
    for (int i = 0; i < offset; i++) {
      sum += data[i];
    }

    // receive, add up & print sums of all other process by mpi_recv
    i = 1;
    /*@
      @ loop invariant 1 <= i <= num_procs;
      @ loop invariant getFirst(get_type(protocol)) ==
      @   getNext(split (getFirst(\at(get_type(protocol),LoopEntry)),i));
      @ loop invariant getNext(get_type(protocol)) ==
      @   getNext(\at(get_type(protocol),LoopEntry));
      @ loop assigns i, protocol, sum;
      @ loop variant num_procs - i;
      @ */
    while (i < num_procs) {
      int tmp = 0;
      /*@ ghost
        unroll();
        assoc();
      */
      MPI_Recv(&tmp, 1, MPI_INT, i, 1, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      sum += tmp;
      i ++;
    }
    // printf("sum: %i \n", sum);
    //@ ghost toskip();

  } else {
    int sum = 0;

    // receive & add up elements from process 0 by mpi_recv
    /*@ ghost
    l1:;
    int j = 1;
    /@ loop invariant 1 <= j <= my_rank;
     @ loop invariant getFirst(get_type(protocol)) ==
     @   getNext(split(getFirst(\at(get_type(protocol),l1)),j));
     @ loop invariant getNext(get_type(protocol)) ==
     @   getNext(\at(get_type(protocol),l1));
     @ loop assigns protocol, j;
     @ loop variant my_rank - j;
     @/
    while (j < my_rank) {
      unroll();
      assoc();
      toskip();
      j++;
    }
    unroll();
    assoc();
    */
    MPI_Recv(data, offset, MPI_INT, 0, 1, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    /*@ ghost
      j++;
      /@ loop invariant my_rank+1 <= j <= num_procs;
       @ loop invariant getFirst(get_type(protocol)) ==
       @   getNext(split(getFirst(\at(get_type(protocol),l1)),j));
       @ loop invariant getNext(get_type(protocol)) ==
       @   getNext(\at(get_type(protocol),l1));
       @ loop assigns protocol, j;
       @ loop variant num_procs - j;
       @/
      while (j < num_procs) {
        unroll();
        assoc();
        toskip();
        j++;
      }
      toskip();
    */

    /*@
      @ loop invariant 0 <= i <= offset;
      @ loop assigns sum, i;
      @ loop variant offset - i;
      @ */
    for (int i = 0; i < offset; i++) {
      sum += data[i];
    }

    /*@ ghost
    l2:;
    j = 1;
    /@ loop invariant 1 <= j <= my_rank;
     @ loop invariant getFirst(get_type(protocol)) ==
     @   getNext(split(getFirst(\at(get_type(protocol),l2)),j));
     @ loop invariant getNext(get_type(protocol)) ==
     @   getNext(\at(get_type(protocol),l2));
     @ loop assigns protocol, j;
     @ loop variant my_rank - j;
     @/
    while (j < my_rank) {
      unroll();
      assoc();
      toskip();
      j++;
    }
    unroll();
    assoc();
    */

    // send total sum of received elements back to process 0 by mpi_send
    MPI_Ssend(&sum, 1, MPI_INT, 0, 1, MPI_COMM_WORLD);

    /*@ ghost
      j++;
      /@ loop invariant my_rank+1 <= j <= num_procs;
       @ loop invariant getFirst(get_type(protocol)) ==
       @   getNext(split(getFirst(\at(get_type(protocol),l2)),j));
       @ loop invariant getNext(get_type(protocol)) ==
       @   getNext(\at(get_type(protocol),l2));
       @ loop assigns protocol, j;
       @ loop variant num_procs - j;
       @/
      while (j < num_procs) {
        unroll();
        assoc();
        toskip();
        j++;
      }
      toskip();
    */
  }

  MPI_Finalize();
  //@ assert \false;
  return 0;
}

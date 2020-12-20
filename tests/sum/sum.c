#include "mpi.h"
#include <stdio.h> 
#include <stdlib.h>


int main(int argc, char **argv){
  int my_rank = 0, num_procs = 0;

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &my_rank);
  MPI_Comm_size(MPI_COMM_WORLD, &num_procs);

  int max_length = 1000; 
  int length = (int)(max_length / num_procs); 
  int offset = length / num_procs; 

  if (my_rank == 0) {

    // initialize array, size is fixed to 1000 elements 
    // only consider first (int)(#processes / 1000) elements 
    int data[max_length]; 
    
    // fill array with some numbers  
    // printf("array: "); 
    /*@ 
      loop invariant 0 <= i <= length; 
      loop assigns data[0 .. length-1], i;
      loop variant length - i; 
    */
    for (int i = 0; i < length; i++) {
      // data[i] = 1; 
      data[i] = (i * 17 * 43) % 7; 
      // printf("%i ", data[i]);
    } 
    // printf("\n");

    // distribute array to other processes by mpi_ssend 
    int i = 1;
    /*@
      loop invariant 1 <= i <= num_procs; 
      loop invariant getFirst(get_type(protocol)) ==
        getNext(split (getFirst(\at(get_type(protocol),LoopEntry)),i));
      loop invariant getNext(get_type(protocol)) ==
        getNext(\at(get_type(protocol),LoopEntry));
      loop assigns protocol, i; 
      loop variant num_procs - i;
    */
    while (i < num_procs) {
      /*@ ghost 
        unroll();
        assoc();
      */ 
      MPI_Ssend(&data[i*offset], offset, MPI_INT, i, 1, MPI_COMM_WORLD);
      i++;
    }

    // sum up the part of array belonging to process 0 
    int sum = 0; 
    /*@
      loop invariant 0 <= i <= offset; 
      loop assigns i, sum; 
      loop variant offset - i; 
    */
    for (int i = 0; i < offset; i++) {
      sum += data[i]; 
    }

    // receive, add up & print sums of all other process by mpi_recv 
    i = 1; 
    /*@
      loop invariant 1 <= i <= num_procs; 
      loop invariant getFirst(get_type(protocol)) ==
        getNext(split (getFirst(\at(get_type(protocol),LoopEntry)),i));
      loop invariant getNext(get_type(protocol)) ==
        getNext(\at(get_type(protocol),LoopEntry));
      loop assigns i, protocol; 
      loop variant num_procs - i; 
    */
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


  } else {

    
    // use array of max_length to avoid dynamic memory allocation
    int data[max_length]; 
    int sum = 0; 

    // receive & add up elements from process 0 by mpi_recv 
    /*@ ghost 
      unroll(); 
      assoc(); 
    */
    MPI_Recv(&data, offset, MPI_INT, 0, 1, MPI_COMM_WORLD, MPI_STATUS_IGNORE); 
      
    /*@
      loop invariant 0 <= i <= offset; 
      loop assigns sum, i; 
      loop variant offset - i; 
    */
    for (int i = 0; i < offset; i++) {
      sum += data[i];
    }

    /*
     ghost loop that unrolls foreach so long 
     that the message fits to the rank of the respective process
    */
   
    /*@ ghost 
      int i = 0; 
      l1:; 
      /@
        loop invariant 0 <= i <= my_rank + 1; 
        loop invariant getFirst(get_type(protocol)) ==
          getNext(split (getFirst(\at(get_type(protocol),l1)),i));
        loop invariant getNext(get_type(protocol)) ==
          getNext(\at(get_type(protocol),l1));
        loop assigns protocol, i; 
        loop variant my_rank + 1 - i; 
      @/
      while (i < my_rank) {
        unroll(); 
        assoc();
        toskip();  
        i++;
      }
    */

    // send total sum of received elements back to process 0 by mpi_send 
    /*@ ghost 
      unroll(); 
      assoc(); 
    */
    MPI_Ssend(&sum, 1, MPI_INT, 0, 1, MPI_COMM_WORLD); 

    /*@ ghost 
      int j = my_rank+1; 
      l2:; 
      /@
        loop invariant 0 <= j <= my_rank + 1; 
        loop invariant getFirst(get_type(protocol)) ==
          getNext(split (getFirst(\at(get_type(protocol),l2)),j));
        loop invariant getNext(get_type(protocol)) ==
          getNext(\at(get_type(protocol),l2));
        loop assigns protocol, j; 
        loop variant my_rank + 1 - j; 
      @/
      while (j < num_procs) {
        unroll(); 
        assoc();
        toskip();  
        j++;
      }
    */
  }
  MPI_Finalize();
  return 0;
}

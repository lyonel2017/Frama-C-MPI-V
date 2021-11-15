#include "mpi.h"
#include <stdio.h>
#include <stdlib.h>

/*@ axiomatic Sum {
  @   logic integer sum{L}(int *t, integer i, integer j)
  @        reads t[..] ;
  @   axiom sum1{L} :
  @     \forall int *t, integer i, j; j <= i ==> sum(t,i,j) == 0;
  @   axiom sum2{L} :
  @     \forall int *t, integer i, j; i < j ==>
  @       sum(t,i,j) == sum(t,i,j-1) + t[j-1];
  @   lemma sum3{L} :
  @     \forall int *t, integer i, j, k;
  @       0 <= i <= j <= k ==>
  @         sum(t,i,k) == sum(t,i,j) + sum(t,j,k);
  @   lemma sum_4{L1,L2} :
  @     \forall int *t1, int* t2, integer i, j;
  @       (\forall integer k; i <= k < j ==> \at(t1[k],L1) == \at(t2[k],L2)) ==>
  @       \at(sum(t1,i,j),L1) == \at(sum(t2,i,j),L2);
  @ }
  @*/

/*@ axiomatic Protocol {
  @ logic logic_protocol f (\list<int> l);
  @}
*/

#define MAX_LENGTH 1000

/*@ requires \valid(t+(0..(MAX_LENGTH-1)));
  @ ensures \initialized(t + (0 .. (MAX_LENGTH-1)));
  @ assigns t[0 .. (MAX_LENGTH-1)];
*/
void init_array (int* t);

//frama-c-gui -mpi-v -wp-driver ../../share/mpi.driver,the_protocol.driver,size.driver sum.c

int main(int argc, char **argv){
  int my_rank = 0, num_procs = 0, offset = 1, active_procs = 0;
  int data[MAX_LENGTH];

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &my_rank);
  MPI_Comm_size(MPI_COMM_WORLD, &num_procs);

  if (num_procs <= MAX_LENGTH){
    offset = MAX_LENGTH / num_procs;
    active_procs = num_procs;
  } else{
    offset = 1;
    active_procs = MAX_LENGTH;
  }

  if (my_rank == 0) {
    // initialize array
    init_array(data);
    // send a ghost array to other processes
    /*@ ghost
      @ int g[MAX_LENGTH];
      @ /@ loop invariant 0 <= i <= MAX_LENGTH;
      @    loop invariant \forall integer k; 0 <= k < i ==> g[k] == data[k];
      @    loop invariant \valid(g + (0 .. (i-1)));
      @    loop invariant \initialized(g + (0 .. (i-1)));
      @    loop assigns g[0 .. (MAX_LENGTH-1)], i;
      @  @/
      @ for (int i = 0; i < MAX_LENGTH; i++) {
      @ g[i] = data[i];
      @ }
      @ MPI_GIntBcast(g, MAX_LENGTH, 0);*/

    //@ ghost simpl();
    /*@ assert get_type(protocol) == f(to_list(&g[0], 0, MAX_LENGTH));*/

    // distribute array to other processes by mpi_ssend
    int i = 1;
    /*@ loop invariant 1 <= i <= active_procs;
      @ loop invariant getFirst(get_type(protocol)) ==
      @   getNext(split (getFirst(\at(get_type(protocol),LoopEntry)),i));
      @ loop invariant getNext(get_type(protocol)) ==
      @   getNext(\at(get_type(protocol),LoopEntry));
      @ loop invariant \forall integer j; i != active_procs ==> 0 <= j < offset
                                          ==> (i * offset) + j < MAX_LENGTH;
      @ loop assigns protocol, i;
      @ loop variant active_procs - i;
      @ */
    while (i < active_procs) {
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
      @ loop invariant sum == sum(&data[0],0,i);
      @ loop assigns i, sum;
      @ loop variant offset - i;
      @*/
    for (int i = 0; i < offset; i++) {
      sum += data[i];
    }

    // receive, add up & print sums of all other process by mpi_recv
    i = 1;
    /*@
      @ loop invariant 1 <= i <= active_procs;
      @ loop invariant getFirst(get_type(protocol)) ==
      @   getNext(split (getFirst(\at(get_type(protocol),LoopEntry)),i));
      @ loop invariant isSkip(getNext(get_type(protocol)));
      @ loop invariant sum == sum(&data[0],0,i*offset);
      @ loop invariant i < active_procs  ==> (i+1) * offset <= MAX_LENGTH;
      @ loop assigns i, protocol, sum;
      @ loop variant active_procs - i;
      @ */
    while (i < active_procs) {
      int tmp = 0;
      /*@ ghost
        unroll();
        assoc();
      */
      MPI_Recv(&tmp, 1, MPI_INT, i, 1, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      /*@ assert tmp == sum(&g[0],i*offset,(i+1)*offset);*/
      /*@ assert tmp == sum(&data[0],i*offset,(i+1)*offset);*/
      sum += tmp;
      i ++;
    }
    /*@ assert sum == sum(&data[0],0,MAX_LENGTH);*/
    //@ ghost toskip();

  } else {
    if (my_rank < active_procs){
      int sum = 0;

      /*@ ghost
        @ int g[MAX_LENGTH];
        @ MPI_GIntBcast(g, MAX_LENGTH, 0);*/

      //@ ghost simpl();
      /*@ assert get_type(protocol) == f(to_list(&g[0], 0, MAX_LENGTH));*/
    l11:;
      // receive & add up elements from process 0 by mpi_recv
      /*@ ghost
          l1:;
          int j = 1;
          /@ loop invariant 1 <= j <= my_rank;
           @ loop invariant getFirst(get_type(protocol)) ==
           @   getNext(split(getFirst(\at(get_type(protocol),l1)),j));
           @ loop invariant getNext(get_type(protocol)) ==
           @   getNext(\at(get_type(protocol),l1));
           @ loop invariant \forall integer i; j != active_procs ==> 0 <= i < offset
           @   ==> (j * offset) + i < MAX_LENGTH;
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
      /*@ assert \forall integer k; 0 <= k < offset ==> g[my_rank*offset + k] == data[k];*/
      /*@ ghost
        j++;
        /@ loop invariant my_rank+1 <= j <= active_procs;
         @ loop invariant getFirst(get_type(protocol)) ==
         @   getNext(split(getFirst(\at(get_type(protocol),l1)),j));
         @ loop invariant getNext(get_type(protocol)) ==
         @   getNext(\at(get_type(protocol),l1));
         @ loop assigns protocol, j;
         @ loop variant active_procs - j;
         @/
        while (j < active_procs) {
          unroll();
          assoc();
          toskip();
          j++;
        }
        toskip();
      */

      /*@ loop invariant 0 <= i <= offset;
        @ loop assigns sum, i;
        @ loop invariant sum == sum(&data[0],0,i);
        @ loop invariant sum == sum(&g[0],my_rank*offset,my_rank*offset + i);
        @ loop variant offset - i;
        @ */
      for (int i = 0; i < offset; i++) {
        sum += data[i];
      }
      /*@ assert get_type(protocol) == getNext(\at(get_type(protocol),l11));*/

      /*@ ghost
        l2:;
        j = 1;
        /@ loop invariant 1 <= j <= my_rank;
         @ loop invariant getFirst(get_type(protocol)) ==
         @   getNext(split(getFirst(\at(get_type(protocol),l2)),j));
         @ loop invariant getNext(get_type(protocol)) ==
         @   getNext(\at(get_type(protocol),l2));
         @ loop invariant (j+1) * offset <= MAX_LENGTH;
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
        /@ loop invariant my_rank+1 <= j <= active_procs;
         @ loop invariant getFirst(get_type(protocol)) ==
         @   getNext(split(getFirst(\at(get_type(protocol),l2)),j));
         @ loop invariant getNext(get_type(protocol)) ==
         @   getNext(\at(get_type(protocol),l2));
         @ loop assigns protocol, j;
         @ loop variant active_procs - j;
         @/
        while (j < active_procs) {
          unroll();
          assoc();
          toskip();
          j++;
        }
        toskip();
      */
    }
    else {

      /*@ ghost
        int g[MAX_LENGTH];
        MPI_GIntBcast(g, MAX_LENGTH, 0);

        simpl();
        /@ assert get_type(protocol) == f(to_list(&g[0], 0, MAX_LENGTH));@/

        l3:;
        int j = 1;
        /@ loop invariant 1 <= j <= active_procs;
         @ loop invariant getFirst(get_type(protocol)) ==
         @   getNext(split(getFirst(\at(get_type(protocol),l3)),j));
         @ loop invariant getNext(get_type(protocol)) ==
         @   getNext(\at(get_type(protocol),l3));
         @ loop assigns protocol, j;
         @ loop variant active_procs - j;
         @/
        while (j < active_procs) {
           unroll();
           assoc();
           toskip();
           j++;
        }
        toskip();
        l4:;
        j = 1;
        /@ loop invariant 1 <= j <= active_procs;
         @ loop invariant getFirst(get_type(protocol)) ==
         @   getNext(split(getFirst(\at(get_type(protocol),l4)),j));
         @ loop invariant isSkip(getNext(get_type(protocol)));
         @ loop assigns protocol, j;
         @ loop variant active_procs - j;
         @/
        while (j < active_procs) {
           unroll();
           assoc();
           toskip();
           j++;
        }

        toskip();
       */
    }
  }
  MPI_Finalize();
  // assert \false;
  return 0;
}

/**
 * Parallel dot product program.
 *
 * Adapted from:
 *   P.S. Pacheco. Parallel Programming with MPI. Morgan Kaufmann, 1997.
 *   parallel_dot1.c example, Chap.5, p.76
 *s
 * Version: $Id: parallel_dot.c 4635 2015-06-09 14:05:04Z edrdo $
 * ParTypes - http://gloss.di.fc.ul.pt/ParTypes
 */
#include <stdio.h>
#include <mpi.h>

#define MAXLEN 1000000

/*@ requires len > 0;
  @ requires \valid(v + (0..(len-1)));
  @ assigns v[0 .. len-1];
  @*/
void Scan_vector(float* v, int len);

/*@ requires \valid(x + (0..(n-1)));
  @ requires \valid(y + (0..(n-1)));
  @ requires n > 0;
  @ assigns \result;
*/
float Serial_dot(float *x, float *y, int n);

/*@ assigns \nothing;
  @ ensures MAXLEN > \result > 0;
  @*/
int getProblemSize(int procs);

/*@ axiomatic MPI_aux_driver{
  @ logic logic_protocol protocol_1 (\list<int> l);
  @ logic logic_protocol protocol_2 (\list<int> l);
  @ logic logic_protocol protocol_3;
  @ logic logic_protocol protocol_4;
}*/

//frama-c-gui -mpi-v -wp-weak-int-model -wp-driver ../../share/mpi.driver,the_protocol.driver,size.driver parallel_dot_annotated.c

/**
 * CHANGES:
 * 1. Send -> Ssend
 * 2. status -> MPI_STATUS_IGNORE
 **/
int main(int argc, char** argv)
{
  int    procs = 0, rank = 0, n = 0, i = 0;
  float  dot = 0, local_dot = 0, remote_dot = 0;
  float  local_x[MAXLEN];
  float  local_y[MAXLEN];
  float  temp[MAXLEN];

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &procs);

  if (rank == 0) {
    n = getProblemSize(procs);
  }

  MPI_Bcast(&n, 1, MPI_INT, 0, MPI_COMM_WORLD);

  /*@ requires get_type(protocol) == protocol_1(to_list(&n, 0, 1));
    @ assigns protocol, temp[0.. MAXLEN - 1], local_x[0.. MAXLEN - 1],i;
    @ ensures get_type(protocol) == protocol_2(to_list(&n, 0, 1));*/
  if (rank == 0) {
    Scan_vector (local_x, n);
    /*@ loop invariant 1 <= i <= procs;
      @ loop invariant procs > 1 ==> getFirst(get_type(protocol)) ==
      @   getNext(split(getFirst(\at(get_type(protocol),LoopEntry)),i));
      @ loop invariant procs == 1 ==> get_type(protocol) == \at(get_type(protocol),LoopEntry);
      @ loop invariant getNext(get_type(protocol)) ==
      @   getNext(\at(get_type(protocol),LoopEntry));
      @ loop assigns protocol, i, temp[0..1000000-1];
      @ loop variant procs - i;
      @*/
    for (i = 1; i < procs; i++) {
      Scan_vector(temp, n);
      //@ ghost unroll();
      //@ ghost assoc();
      MPI_Ssend(temp, n, MPI_INT, i, 0, MPI_COMM_WORLD);
    }
    //@ ghost toskip();
  }
  else {
    /*@ ghost
      l1:;
      int j = 1;
      /@ loop invariant 1 <= j <= rank;
       @ loop invariant getFirst(get_type(protocol)) ==
       @  getNext(split(getFirst(\at(get_type(protocol),l1)),j));
       @ loop invariant getNext(get_type(protocol)) ==
       @  getNext(\at(get_type(protocol),l1));
       @ loop assigns protocol, j;
       @ loop variant rank - j;
       @/
      while (j < rank) {
        unroll();
        assoc();
        toskip();
        j++;
      }

      unroll();
      assoc();
      @*/
    MPI_Recv(local_x, n, MPI_INT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    /*@ ghost
      j++;
      /@ loop invariant rank + 1 <= j <= procs;
       @ loop invariant getFirst(get_type(protocol)) ==
       @  getNext(split(getFirst(\at(get_type(protocol),l1)),j));
       @ loop invariant getNext(get_type(protocol)) ==
       @  getNext(\at(get_type(protocol),l1));
       @ loop assigns protocol, j;
       @ loop variant procs - j;
       @/
      while (j < procs) {
        unroll();
        assoc();
        toskip();
        j++;
      }
      toskip();
      @*/
  }

  /*@ requires get_type(protocol) == protocol_2(to_list(&n, 0, 1));
    @ assigns protocol, temp[0.. MAXLEN - 1], local_y[0.. MAXLEN - 1],i;
    @ ensures get_type(protocol) == protocol_3;*/
  if (rank == 0) {
    Scan_vector (local_y, n);
    /*@ loop invariant 1 <= i <= procs;
      @ loop invariant procs > 1 ==> getFirst(get_type(protocol)) ==
      @   getNext(split(getFirst(\at(get_type(protocol),LoopEntry)),i));
      @ loop invariant procs == 1 ==> get_type(protocol) == \at(get_type(protocol),LoopEntry);
      @ loop invariant getNext(get_type(protocol)) ==
      @   getNext(\at(get_type(protocol),LoopEntry));
      @ loop assigns protocol, i, temp[0..1000000-1];
      @ loop variant procs - i;
      @*/
    for(i = 1; i < procs; i++) {
        Scan_vector (temp, n);
        //@ ghost unroll();
        //@ ghost assoc();
        MPI_Ssend(temp, n, MPI_INT, i, 0, MPI_COMM_WORLD);
    }
    //@ ghost toskip();
  }
  else {
    /*@ ghost
      l2:;
      int j = 1;
      /@ loop invariant 1 <= j <= rank;
       @ loop invariant getFirst(get_type(protocol)) ==
       @  getNext(split(getFirst(\at(get_type(protocol),l2)),j));
       @ loop invariant getNext(get_type(protocol)) ==
       @  getNext(\at(get_type(protocol),l2));
       @ loop assigns protocol, j;
       @ loop variant rank - j;
       @/
      while (j < rank) {
        unroll();
        assoc();
        toskip();
        j++;
      }
      unroll();
      assoc();
      @*/
    MPI_Recv(local_y, n, MPI_INT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    /*@ ghost
      j++;
      /@ loop invariant rank + 1 <= j <= procs;
       @ loop invariant getFirst(get_type(protocol)) ==
       @  getNext(split(getFirst(\at(get_type(protocol),l2)),j));
       @ loop invariant getNext(get_type(protocol)) ==
       @  getNext(\at(get_type(protocol),l2));
       @ loop assigns protocol, j;
       @ loop variant procs - j;
       @/
      while (j < procs) {
        unroll();
        assoc();
        toskip();
        j++;
      }
      toskip();
      @*/
  }

  // Local computation followed by reduction
  local_dot = Serial_dot(local_x, local_y, n);
  MPI_Allreduce(&local_dot, &dot, 1, MPI_INT, MPI_SUM, MPI_COMM_WORLD);

  // REMOVED: no I/O
  // Print result
  // printf("Result: %f\n", dot);

  // Print local at each process

  /*@ requires get_type(protocol) == protocol_4;
    @ assigns remote_dot,i,protocol;
    @ ensures isSkip(get_type(protocol));*/
  if (rank == 0) {
    /*@ loop invariant 1 <= i <= procs;
      @ loop invariant procs > 1 ==> getFirst(get_type(protocol)) ==
      @   getNext(split(getFirst(\at(get_type(protocol),LoopEntry)),i));
      @ loop invariant procs == 1 ==> get_type(protocol) == \at(get_type(protocol),LoopEntry);
      @ loop invariant getNext(get_type(protocol)) ==
      @   getNext(\at(get_type(protocol),LoopEntry));
      @ loop assigns protocol, i, remote_dot;
      @ loop variant procs - i;
      @*/
    for (i = 1; i < procs; i++) {
      //@ ghost unroll();
      //@ ghost assoc();
      MPI_Recv(&remote_dot, 1, MPI_INT, i, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);

      // REMOVED: no I/O
      // printf("Result at process %d : %f\n", i, remote_dot);
    }
    //@ ghost toskip();
  }
  else {
    /*@ ghost
      l3:;
      int j = 1;
      /@ loop invariant 1 <= j <= rank;
       @ loop invariant getFirst(get_type(protocol)) ==
       @  getNext(split(getFirst(\at(get_type(protocol),l3)),j));
       @ loop invariant getNext(get_type(protocol)) ==
       @  getNext(\at(get_type(protocol),l3));
       @ loop assigns protocol, j;
       @ loop variant rank - j;
       @/
      while (j < rank) {
        unroll();
        assoc();
        toskip();
        j++;
      }
      unroll();
      assoc();
      @*/

    MPI_Ssend(&local_dot, 1, MPI_INT, 0, 0, MPI_COMM_WORLD);
    /*@ ghost
      j++;
      /@ loop invariant rank + 1 <= j <= procs;
       @ loop invariant getFirst(get_type(protocol)) ==
       @  getNext(split(getFirst(\at(get_type(protocol),l3)),j));
       @ loop invariant getNext(get_type(protocol)) ==
       @  getNext(\at(get_type(protocol),l3));
       @ loop assigns protocol, j;
       @ loop variant procs - j;
       @/
      while (j < procs) {
        unroll();
        assoc();
        toskip();
        j++;
      }
      toskip();
      @*/
  }

  MPI_Finalize();
  return 0;
}

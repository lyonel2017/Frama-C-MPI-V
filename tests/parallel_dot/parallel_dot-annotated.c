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


//@ ensures \valid(v + (0..(len-1)));
void Scan_vector(float* v, int len);


float  Serial_dot(float *x, float *y, int n);

/*@
  @ ensures \result == MAXLEN && \result % procs == 0;
  @*/
int getProblemSize(int procs);



/**
 * CHANGES:
 * 1. Send -> Ssend
 * 2. n -> 1000000 (static problem size)
 * 3. status -> MPI_STATUS_IGNORE
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

  if (rank == 0) {
    Scan_vector (local_x, n);
    /*@ loop invariant 1 <= i <= procs;
      @ loop invariant getFirst(get_type(protocol)) ==
      @   getNext(split(getFirst(\at(get_type(protocol),LoopEntry)),i));
      @ loop invariant getNext(get_type(protocol)) ==
      @   getNext(\at(get_type(protocol),LoopEntry));
      @ loop assigns protocol, i, temp[0..1000000-1];
      @ loop variant procs - i;
      @*/
    for (i = 1; i < procs; i++) {
      //@ ghost unroll();
      //@ ghost assoc();
      Scan_vector(temp, 1000000);
      MPI_Ssend(temp, 1000000, MPI_FLOAT, i, 0, MPI_COMM_WORLD);
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
    MPI_Recv(local_x, 1000000, MPI_FLOAT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
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

  if (rank == 0) {
    Scan_vector (local_y, n);
    /*@ loop invariant 1 <= i <= procs;
      @ loop invariant getFirst(get_type(protocol)) ==
      @   getNext(split(getFirst(\at(get_type(protocol),LoopEntry)),i));
      @ loop invariant getNext(get_type(protocol)) ==
      @   getNext(\at(get_type(protocol),LoopEntry));
      @ loop assigns protocol, i, temp[0..1000000-1];
      @ loop variant procs - i;
      @*/
    for(i = 1; i < procs; i++) {
        //@ ghost unroll();
        //@ ghost assoc();
        Scan_vector (temp, 1000000);
        MPI_Ssend(temp, 1000000, MPI_FLOAT, i, 0, MPI_COMM_WORLD);
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
    MPI_Recv(local_y, 1000000, MPI_FLOAT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
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
  MPI_Allreduce(&local_dot, &dot, 1, MPI_FLOAT, MPI_SUM, MPI_COMM_WORLD);

  // REMOVED: no I/O
  // Print result
  // printf("Result: %f\n", dot);

  // Print local at each process
  if (rank == 0) {
    /*@ loop invariant 1 <= i <= procs;
      @ loop invariant getFirst(get_type(protocol)) ==
      @   getNext(split(getFirst(\at(get_type(protocol),LoopEntry)),i));
      @ loop invariant getNext(get_type(protocol)) ==
      @   getNext(\at(get_type(protocol),LoopEntry));
      @ loop assigns protocol, i, remote_dot;
      @ loop variant procs - i;
      @*/
    for (i = 1; i < procs; i++) {
      //@ ghost unroll();
      //@ ghost assoc();
      MPI_Recv(&remote_dot, 1, MPI_FLOAT, i, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);

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
    MPI_Ssend(&local_dot, 1, MPI_FLOAT, 0, 0, MPI_COMM_WORLD);
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
  //@ assert \false;
  return 0;
}








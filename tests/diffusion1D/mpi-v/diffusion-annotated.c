/**
 * ParTypes - http://gloss.di.fc.ul.pt/ParTypes
 *
 * The 1-D heat diffusion program.
 *
 * Adapted from:
 *   FEVS: A Functional Equivalence Verification Suite.
 *   http://vsl.cis.udel.edu/fevs/index.html
 *
 * Version: $Id: diffusion1D.prot 4690 2015-06-24 10:18:56Z edrdo $
 */

// MPI header
#include <mpi.h>

// Program definitions
#define MAXLEN 10000

// External functions
int getNumIterations(void);
//@ ensures \result == MAXLEN && \result % procs == 0;
int getProblemSize(int procs);
int getWstep();

//@  assigns data[(rank*len) .. ((rank+1)*len-1)];
void getInitialData(int rank, float* data, int len);
int compute(float* u, float* u_new, int len, int wstep);

// n fixed to MAXLEN
// status changed to MPI_STATUS_IGNORE
// changed send to ssend
int main(int argc, char** argv) {
  int procs;  // process count
  int rank; // process rank */
  int n; // number of discrete points including endpoints
  int local_n; // size of local data = n / procs
  int numIter; // number of time steps
  int wstep;  // write frame every this many time steps
  int i, iter, start, stop, left, right;
  MPI_Status status;
  float u[MAXLEN+2]; // temperature function
  float u_new[MAXLEN+2];  // temp. used to update u
  float buf[MAXLEN+1]; // Local buffer used on rank 0
  MPI_Init(&argc, &argv);
  MPI_Comm_size(MPI_COMM_WORLD, &procs);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);

  if (rank == 0) {
    numIter = getNumIterations();
    n = getProblemSize(procs);
    wstep = getWstep();
  }
  MPI_Bcast(&n, 1, MPI_INT, 0, MPI_COMM_WORLD);
  //inserted, not necessary if bcast implies this assignment
  n = getProblemSize(procs);
  MPI_Bcast(&numIter, 1, MPI_INT, 0, MPI_COMM_WORLD);
  MPI_Bcast(&wstep, 1, MPI_INT, 0, MPI_COMM_WORLD);
  local_n = n / procs;
  /*@ loop invariant 1 <= i <= local_n + 1;
    @ loop assigns i, u[1..(local_n+1)];
    @ loop variant local_n + 1 - i;
    @*/
  for (int i = 1; i <= local_n; i++) {
    u[i] = 0;
  }
  //@ assert \valid(u + (1..local_n));
  if (rank == 0) {
    getInitialData(0, &u[1], local_n);
    /*@ loop invariant 1 <= i <= procs;
      @ loop invariant getFirst(get_type(protocol)) ==
      @   getNext(split(getFirst(\at(get_type(protocol),LoopEntry)),i));
      @ loop invariant getNext(get_type(protocol)) ==
      @   getNext(\at(get_type(protocol),LoopEntry));
      @ loop assigns protocol, i, buf[0..(procs*local_n-1)];
      @ loop variant procs - i;
      @*/
    for (i = 1; i < procs; i++) {
      getInitialData(i, buf, local_n);
      //@ ghost unroll();
      //@ ghost assoc();
      MPI_Ssend(buf, local_n, MPI_FLOAT, i, 0, MPI_COMM_WORLD);
    }
    //@ ghost toskip();
  } else {
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
    MPI_Recv(&u[1], local_n, MPI_FLOAT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
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
  start = rank == 0 ? 2 : 1;
  stop  = rank == procs - 1 ? n - 1 : n;
  left  = rank - 1;
  right = rank + 1;
  // for (iter = 0; iter < numIter; iter++) {

  if (rank == 0) {
    //@ ghost l2:;
    //@ ghost unroll();
    //@ ghost assoc();
    MPI_Recv(&u[local_n+1], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    /*@ ghost
      int j = 2;
      /@ loop invariant 2 <= j <= procs;
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
  else if (rank == procs-1) {
    /*@ ghost
      l3:;
      int j = 1;
      /@ loop invariant 1 <= j <= procs-1;
       @ loop invariant getFirst(get_type(protocol)) ==
       @  getNext(split(getFirst(\at(get_type(protocol),l3)),j));
       @ loop invariant getNext(get_type(protocol)) ==
       @  getNext(\at(get_type(protocol),l3));
       @ loop assigns protocol, j;
       @ loop variant procs - 1 - j;
       @/
      while (j < procs - 1) {
        unroll();
        assoc();
        toskip();
        j++;
      }
      unroll();
      assoc();
      @*/
    MPI_Ssend(&u[1], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD);
    //@ ghost toskip();
  }
  else {
    /*@ ghost
      l4:;
      int j = 1;
      /@ loop invariant 1 <= j <= rank;
       @ loop invariant getFirst(get_type(protocol)) ==
       @  getNext(split(getFirst(\at(get_type(protocol),l4)),j));
       @ loop invariant getNext(get_type(protocol)) ==
       @  getNext(\at(get_type(protocol),l4));
       @ loop assigns protocol, j;
       @ loop variant (rank - 1) - j;
       @/
      while (j < rank-1) {
        unroll();
        assoc();
        toskip();
        j++;
      }
      unroll();
      assoc();
      @*/
    MPI_Recv(&u[local_n+1], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    //@ ghost unroll();
    //@ ghost assoc();
    MPI_Ssend(&u[1], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD);
    /*@ ghost
      j = rank+1;
      /@ loop invariant rank+1 <= j <= procs;
       @ loop invariant getFirst(get_type(protocol)) ==
       @  getNext(split(getFirst(\at(get_type(protocol),l4)),j));
       @ loop invariant getNext(get_type(protocol)) ==
       @  getNext(\at(get_type(protocol),l4));
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
  //   if (rank == 0) {
  //     MPI_Send(&u[local_n], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
  //   } else if (rank == procs - 1) {
  //     MPI_Recv(&u[0], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD, &status);
  //   } else {
  //     //ERROR Start Missing send
  //     MPI_Send(&u[local_n], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
  //     //ERROR End Missing send
  //     MPI_Recv(&u[0], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD, &status);
  //   }
  //   compute(u, u_new, local_n, wstep);
  // }
  MPI_Finalize();
  // //@ assert \false;
  return 0;
}


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
#define NUMITER 10000

// External functions
//@ ensures \result == NUMITER;
int getNumIterations();
//@ ensures \result == MAXLEN && \result % procs == 0;
int getProblemSize(int procs);
int getWstep();

//@  assigns data[(rank*len) .. ((rank+1)*len-1)];
void getInitialData(int rank, float* data, int len);
int compute(float* u, float* u_new, int len, int wstep);

/*@ axiomatic MPI_aux_driver{
  @ logic logic_protocol protocol_1;
  @ logic logic_protocol protocol_2;
  @ logic logic_protocol protocol_3;
  @ logic logic_protocol protocol_4;
  @ logic logic_protocol protocol_5;
  @ logic logic_protocol protocol_6;
  @ logic logic_protocol protocol_foo1(integer i);
  @ logic logic_protocol protocol_foo2(integer i);
  @ logic logic_protocol protocol_foo3(integer i);
}*/

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
  numIter = getNumIterations();
  MPI_Bcast(&wstep, 1, MPI_INT, 0, MPI_COMM_WORLD);
  local_n = n / procs;
  /*@ loop invariant 0 <= i <= MAXLEN + 2;
    @ loop assigns i, u[0..(MAXLEN+1)];
    @ loop variant MAXLEN + 2 - i;
    @*/
  for (int i = 0; i < MAXLEN + 2; i++) {
    u[i] = 0;
  }

  /*@ requires get_type(protocol) == protocol_3;
    @ assigns i, u[1..local_n],buf[0..(procs*local_n-1)], protocol;
    @ ensures isSkip(get_type(protocol));
    @*/
  if (rank == 0) {
    getInitialData(0, &u[1], local_n);
    //@ ghost l0:;
    /*@ loop invariant 1 <= i <= procs;
      @ loop invariant i < procs ==> getFirst(get_type(protocol)) ==
      @   getNext(split(getFirst(\at(get_type(protocol),l0)),i));
      @ loop invariant i < procs ==> getNext(get_type(protocol)) ==
      @   getNext(\at(get_type(protocol),l0));
      @ loop invariant i == procs ==> isSkip(get_type(protocol));
      @ loop assigns protocol, i, buf[0..(procs*local_n-1)];
      @ loop variant procs - i;
      @*/
    for (i = 1; i < procs; i++) {
      getInitialData(i, buf, local_n);
      //@ ghost unroll();
      //@ ghost assoc();
      //@ assert getFirst(get_type(protocol)) == protocol_foo1(i);
      MPI_Ssend(buf, local_n, MPI_FLOAT, i, 0, MPI_COMM_WORLD);
      /*@ ghost
        if (i == procs-1) {
          /@ assert getFirst(get_type(protocol)) ==
           @   getNext(split(getFirst(\at(get_type(protocol),l0)),i+1));
           @/
          toskip();
        }
        @*/
    }
  } else {
    /*@ ghost
      l1:;
      int j = 1;
      /@ requires j == 1;
       @ requires get_type(protocol) == protocol_3;
       @ assigns protocol, j;
       @ ensures j == rank;
       @ ensures getFirst(get_type(protocol)) == protocol_foo1(j);
       @ ensures getFirst(getNext(get_type(protocol))) ==
       @   getNext(split(getFirst(\at(get_type(protocol),l1)),j+1));
       @ ensures getNext(getNext(get_type(protocol))) ==
       @   getNext(\at(get_type(protocol),l1));
       @/
      {
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
          //@ assert getFirst(get_type(protocol)) == protocol_foo1(j);
          toskip();
          j++;
        }
        unroll();
        assoc();
      }
      @*/
    //@ assert getFirst(get_type(protocol)) == protocol_foo1(j);
    MPI_Recv(&u[1], local_n, MPI_FLOAT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    /*@ ghost
      j++;
      /@ requires j == rank+1;
       @ requires getFirst(get_type(protocol)) ==
       @   getNext(split(getFirst(\at(get_type(protocol),l1)),j));
       @ requires getNext(get_type(protocol)) ==
       @   getNext(\at(get_type(protocol),l1));
       @ assigns protocol, j;
       @ ensures isSkip(get_type(protocol));
       @/
      {
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
          //@ assert getFirst(get_type(protocol)) == protocol_foo1(j);
          toskip();
          j++;
        }
        toskip();
      }
      @*/
  }
  start = rank == 0 ? 2 : 1;
  stop  = rank == procs - 1 ? n - 1 : n;
  left  = rank - 1;
  right = rank + 1;

  MPI_Finalize();
  // //@ assert \false;
  return 0;
}


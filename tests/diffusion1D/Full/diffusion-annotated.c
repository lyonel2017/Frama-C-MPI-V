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
/*@ requires \valid(u_new + (0..len-1));
  @ requires \valid(u + (0..len-1));
  @ assigns \result,u_new[0..len-1];
  @ ensures \valid(u_new + (0..len-1));
  @*/
int compute(float* u, float* u_new, int len, int wstep);

/*@ axiomatic MPI_aux_driver{
  @ logic logic_protocol protocol_1;
  @ logic logic_protocol protocol_2;
  @ logic logic_protocol protocol_3;
  @ logic logic_protocol protocol_4;
  @ logic logic_protocol protocol_5;
  @ logic logic_protocol protocol_6;
  @ logic logic_protocol protocol_7;
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

  //inserted, not necessary if ssend implies this assignment
  /*@ loop invariant 0 <= i <= MAXLEN + 2;
    @ loop assigns i, u[0..(MAXLEN+1)];
    @ loop variant MAXLEN + 2 - i;
    @*/
  for (int i = 0; i < MAXLEN + 2; i++) {
    u[i] = 0;
  }
  //@ ghost l01:;
  /*@ requires get_type(protocol) == protocol_3;
    @ assigns i, u[1..local_n],buf[0..(procs*local_n-1)], protocol;
    @ ensures get_type(protocol) == protocol_4;
    @*/
  if (rank == 0) {
    getInitialData(0, &u[1], local_n);
    //@ ghost l001:;
    /*@ loop invariant 1 <= i <= procs;
      @ loop invariant i < procs ==> getFirst(get_type(protocol)) ==
      @   getNext(split(getFirst(\at(get_type(protocol),l001)),i));
      @ loop invariant i < procs ==> getNext(get_type(protocol)) ==
      @   getNext(\at(get_type(protocol),l001));
      @ loop invariant i == procs ==> get_type(protocol) ==
      @   getNext(\at(get_type(protocol),l01));
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
           @   getNext(split(getFirst(\at(get_type(protocol),l001)),i+1));
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
       @ ensures get_type(protocol) ==
       @   getNext(\at(get_type(protocol),l01));
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

  //@ assert getFirst(get_type(protocol)) == protocol_4;
  //@ ghost l02:;
  /*@ loop invariant 0 <= iter <= NUMITER;
    @ loop invariant getFirst(get_type(protocol)) ==
    @   getNext(split(getFirst(\at(get_type(protocol),l02)),iter));
    @ loop invariant getNext(get_type(protocol)) ==
    @   getNext(\at(get_type(protocol),l02));
    @ loop assigns protocol, iter, u[local_n+1], u[0], u_new[0..local_n-1];
    @ loop variant NUMITER - iter - 1;
    @*/
  for (iter = 0; iter < NUMITER; iter++) {
    /*@ ghost
      l0:;
      unroll();
      assoc();
      assoc();
      l00:;
    @*/
    /*@ requires getFirst(get_type(protocol)) == protocol_6;
      @ assigns u[local_n+1], protocol;
      @ ensures get_type(protocol) == getNext(\at(get_type(protocol),l00));
      // @ ensures getFirst(get_type(protocol)) == protocol_7;
      @*/
    if (rank == 0) {
      /*@ ghost
        l2:;
        int j = 1;
        /@ loop invariant 1 <= j <= procs-1;
        @ loop invariant getFirst(get_type(protocol)) ==
        @   getNext(split(getFirst(\at(get_type(protocol),l2)),j));
        @ loop invariant getNext(get_type(protocol)) ==
        @   getNext(\at(get_type(protocol),l2));
        @ loop assigns protocol, j;
        @ loop variant procs - 1 - j;
        @/
          while (j < procs - 1) {
            unroll();
            assoc();
            //@ assert getFirst(get_type(protocol)) == protocol_foo2(j);
            toskip();
            j++;
          }
          unroll();
          assoc();
      @*/
      //@ assert getFirst(get_type(protocol)) == protocol_foo2(j);
      MPI_Recv(&u[local_n+1], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      /*@ ghost
        j++;
        // //@ assert getFirst(get_type(protocol)) == protocol_foo2(j);
        toskip();
        //@ assert get_type(protocol) == getNext(\at(get_type(protocol),l2));
      @*/
    }
    else if (rank == procs-1) {
      /*@ ghost
        l3:;
        int j = 1;
        unroll();
        assoc();
        @*/
      //@ assert getFirst(get_type(protocol)) == protocol_foo2(j);
      MPI_Ssend(&u[1], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD);
      /*@ ghost
        j++;
        if (j < procs) {
          /@ loop invariant 2 <= j <= procs;
          @ loop invariant getFirst(get_type(protocol)) ==
          @   getNext(split(getFirst(\at(get_type(protocol),l3)),j));
          @ loop invariant getNext(get_type(protocol)) ==
          @   getNext(\at(get_type(protocol),l3));
          @ loop assigns protocol, j;
          @ loop variant procs - 1 - j;
          @/
          while (j < procs) {
            unroll();
            assoc();
            //@ assert getFirst(get_type(protocol)) == protocol_foo2(j);
            toskip();
            j++;
          }}
        // //@ assert getFirst(get_type(protocol)) == protocol_foo2(j);
        toskip();
        //@ assert get_type(protocol) == getNext(\at(get_type(protocol),l3));
        @*/
    }
    else {
      /*@ ghost
        l4:;
        int j = 1;
        /@ loop invariant 1 <= j <= procs - rank - 1;
        @ loop invariant getFirst(get_type(protocol)) ==
        @   getNext(split(getFirst(\at(get_type(protocol),l4)),j));
        @ loop invariant getNext(get_type(protocol)) ==
        @   getNext(\at(get_type(protocol),l4));
        @ loop assigns protocol, j;
        @ loop variant procs - rank - 1 - j;
        @/
        while (j < procs - rank - 1) {
          unroll();
          assoc();
          //@ assert getFirst(get_type(protocol)) == protocol_foo2(j);
          toskip();
          j++;
        }
        unroll();
        assoc();
        @*/
      //@ assert getFirst(get_type(protocol)) == protocol_foo2(j);
      MPI_Recv(&u[local_n+1], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      /*@ ghost
        j++;
        //@ assert getFirst(get_type(protocol)) ==  getNext(split(getFirst(\at(get_type(protocol),l4)),j));
        //@ assert getNext(get_type(protocol)) ==  getNext(\at(get_type(protocol),l4));
        unroll();
        assoc();
        @*/
      //@ assert getFirst(get_type(protocol)) == protocol_foo2(j);
      MPI_Ssend(&u[1], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD);
      /*@ ghost
        j = procs - rank + 1;
        if (j < procs) {
          /@ loop invariant procs - rank + 1 <= j <= procs;
            @ loop invariant getFirst(get_type(protocol)) ==
            @   getNext(split(getFirst(\at(get_type(protocol),l4)),j));
            @ loop invariant getNext(get_type(protocol)) ==
            @   getNext(\at(get_type(protocol),l4));
            @ loop assigns protocol, j;
            @ loop variant procs - j;
            @/
          while (j < procs) {
            unroll();
            assoc();
            //@ assert getFirst(get_type(protocol)) == protocol_foo2(j);
            toskip();
            j++;
          }}
        // //@ assert getFirst(get_type(protocol)) == protocol_foo2(j);
        toskip();
        //@ assert get_type(protocol) == getNext(\at(get_type(protocol),l4));
        @*/
    }

    //@ assert getFirst(get_type(protocol)) == protocol_7;
    // /*@ requires get_type(protocol) == getNext(\at(get_type(protocol),l00));
    //   @ assigns protocol, u[0];
      // @ ensures getFirst(get_type(protocol)) ==
      // @   getNext(split(getFirst(\at(get_type(protocol),l02)),iter));
      // @ ensures getNext(get_type(protocol)) ==
      // @   getNext(\at(get_type(protocol),l02));
      // @ ensures get_type(protocol) == getNext(getNext(\at(get_type(protocol),l00)));
      // @*/
    if (rank == 0) {
      /*@ ghost
        @ l5:;
        @ int j = 0;
        @ unroll();
        @ assoc();
        @*/
      //@ assert getFirst(get_type(protocol)) == protocol_foo3(j);
      MPI_Ssend(&u[local_n], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
      /*@ ghost
        j++;
        if (j < procs - 1) {
          /@ loop invariant 1 <= j <= procs - 1;
          @ loop invariant getFirst(get_type(protocol)) ==
          @  getNext(split(getFirst(\at(get_type(protocol),l5)),j));
          @ loop invariant getNext(get_type(protocol)) ==
          @  getNext(\at(get_type(protocol),l5));
          @ loop assigns protocol, j;
          @ loop variant procs - 1 - j;
          @/
          while (j < procs - 1) {
            unroll();
            assoc();
            //@ assert getFirst(get_type(protocol)) == protocol_foo3(j);
            toskip();
            j++;
          }}
        // //@ assert getFirst(get_type(protocol)) == protocol_foo3(j);
        toskip();
        //@ assert get_type(protocol) == getNext(\at(get_type(protocol),l5));
        @*/
    } else if (rank == procs - 1) {
        /*@ ghost
        l6:;
        int j = 0;
        /@ loop invariant 0 <= j <= procs - 2;
          @ loop invariant getFirst(get_type(protocol)) ==
          @  getNext(split(getFirst(\at(get_type(protocol),l6)),j));
          @ loop invariant getNext(get_type(protocol)) ==
          @  getNext(\at(get_type(protocol),l6));
          @ loop assigns protocol, j;
          @ loop variant procs - 2 - j;
          @/
        while (j < procs - 2) {
          unroll();
          assoc();
          //@ assert getFirst(get_type(protocol)) == protocol_foo3(j);
          toskip();
          j++;
        }
        unroll();
        assoc();
        @*/
      //@ assert getFirst(get_type(protocol)) == protocol_foo3(j);
      MPI_Recv(&u[0], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      /*@ ghost
      // //@ assert getFirst(get_type(protocol)) == protocol_foo3(j);
      toskip();
      //@ assert get_type(protocol) == getNext(\at(get_type(protocol),l6));
      @*/
    } else {
      /*@ ghost
        l7:;
        int j = 0;
        /@ loop invariant 0 <= j <= rank - 1;
          @ loop invariant getFirst(get_type(protocol)) ==
          @  getNext(split(getFirst(\at(get_type(protocol),l7)),j));
          @ loop invariant getNext(get_type(protocol)) ==
          @  getNext(\at(get_type(protocol),l7));
          @ loop assigns protocol, j;
          @ loop variant rank - 1 - j;
          @/
        while (j < rank - 1) {
          unroll();
          assoc();
          //@ assert getFirst(get_type(protocol)) == protocol_foo3(j);
          toskip();
          j++;
        }
        unroll();
        assoc();
        @*/
      //@ assert getFirst(get_type(protocol)) == protocol_foo3(j);
      MPI_Recv(&u[0], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      /*@ ghost
        j++;
        //@ assert getFirst(get_type(protocol)) ==  getNext(split(getFirst(\at(get_type(protocol),l7)),j));
        //@ assert getNext(get_type(protocol)) ==  getNext(\at(get_type(protocol),l7));
        unroll();
        assoc();
        @*/
      //ERROR Start Missing send
      //@ assert getFirst(get_type(protocol)) == protocol_foo3(j);
      MPI_Ssend(&u[local_n], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
      //ERROR End Missing send
      /*@ ghost
        j++;
        @*/
      /*@ ghost
        @ if (j < procs-1) {
          /@ loop invariant rank + 1 <= j <= procs - 1;
           @ loop invariant getFirst(get_type(protocol)) ==
           @   getNext(split(getFirst(\at(get_type(protocol),l7)),j));
           @ loop invariant getNext(get_type(protocol)) ==
           @   getNext(\at(get_type(protocol),l7));
           @ loop assigns protocol, j;
           @ loop variant procs - 1 - j;
           @/
          while (j < procs - 1) {
            unroll();
            assoc();
            //@ assert getFirst(get_type(protocol)) == protocol_foo3(j);
            toskip();
            j++;
          }}
        // //@ assert getFirst(get_type(protocol)) == protocol_foo3(j);
        toskip();
        @*/
      //@ assert get_type(protocol) == getNext(\at(get_type(protocol),l7));
    }
    compute(u, u_new, local_n, wstep);
  }
  /*@ ghost
    @ toskip();
    @*/
  MPI_Finalize();
  return 0;
}


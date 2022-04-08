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

#include <mpi.h>

#define MAXLEN 10000

/*@ assigns \result;
  @ ensures 0 < \result;*/
int getNumIterations();

/*@ requires 0 < procs;
  @ assigns \result;
  @ ensures 0 < \result <= MAXLEN * procs && \result % procs == 0;*/
int getProblemSize(int procs);

/*@ assigns \result;*/
int getWstep();

//@  assigns data[0 .. (len-1)];
void getInitialData(int rank, int* data, int len);

/*@ requires \valid(u_new + (0..len-1));
  @ requires \valid(u + (0..len-1));
  @ assigns \result,u_new[0..len-1];
  @ ensures \valid(u_new + (0..len-1));
  @*/
int compute(int* u, int* u_new, int len, int wstep);

/*@ axiomatic MPI_aux_driver{
  logic logic_protocol f1 (integer i, integer n);
  logic logic_protocol f2 (integer i);
  logic logic_protocol f3 (integer i);
  logic logic_protocol protocol_1 (integer n);
  logic logic_protocol protocol_2 (integer n, integer inter);
  logic logic_protocol protocol_3 (integer n, integer inter, integer step);
  logic logic_protocol protocol_4 (integer inter);
  logic logic_protocol protocol_5;
  logic logic_protocol protocol_6;
  logic logic_protocol protocol_7;
}*/

//frama-c-gui -mpi-v -wp-weak-int-model -wp-driver ../../share/mpi.driver,the_protocol.driver,size.driver diffusion-annotated.c

int main(int argc, char** argv) {
  int procs;  // process count
  int rank; // process rank */
  int n; // number of discrete points including endpoints
  int local_n; // size of local data = n / procs
  int numIter; // number of time steps
  int wstep;  // write frame every this many time steps
  int i, iter, stop, left, right;
  int u[MAXLEN+2]; // temperature function
  int u_new[MAXLEN+2];  // temp. used to update u
  int buf[MAXLEN+1]; // Local buffer used on rank 0

  MPI_Init(&argc, &argv);
  MPI_Comm_size(MPI_COMM_WORLD, &procs);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);

  if (rank == 0) {
    numIter = getNumIterations();
    n = getProblemSize(procs);
    wstep = getWstep();
  }
  MPI_Bcast(&n, 1, MPI_INT, 0, MPI_COMM_WORLD);
  /*@ ghost simpl();*/
  /*@ assert get_type(protocol) == protocol_1(n);*/
  MPI_Bcast(&numIter, 1, MPI_INT, 0, MPI_COMM_WORLD);
  /*@ ghost simpl();*/
  /*@ assert get_type(protocol) == protocol_2(n,numIter);*/
  MPI_Bcast(&wstep, 1, MPI_INT, 0, MPI_COMM_WORLD);
  /*@ ghost simpl();*/
  /*@ assert get_type(protocol) == protocol_3(n,numIter,wstep);*/
  local_n = n / procs;

  if (rank == 0) {
    getInitialData(0, &u[1], local_n);
    /*@ loop invariant 1 <= i <= procs;
      @ loop invariant getLeft(get_type(protocol)) ==
      @   split_right(getLeft(\at(get_type(protocol),LoopEntry)),i);
      @ loop invariant getRight(get_type(protocol)) ==
      @   getRight(\at(get_type(protocol),LoopEntry));
      @ loop assigns protocol, i, buf[0..(local_n-1)];
      @ loop variant procs - i;
      @*/
    for (i = 1; i < procs; i++) {
      getInitialData(i, buf, local_n);
      //@ ghost unroll();
      //@ ghost assoc();
      MPI_Ssend(buf, local_n, MPI_INT, i, 0, MPI_COMM_WORLD);
    }
    /*@ghost next();*/
  } else {
    /*@ ghost
        split(rank);
        assoc();
        fsimpl();
        unroll();
        assoc();*/
    MPI_Recv(&u[1], local_n, MPI_INT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    /*@ ghost fsimpl();*/
  }
  left  = rank - 1;
  right = rank + 1;

  /*@ assert get_type(protocol) == protocol_4(numIter);*/

  /*@ loop invariant 0 <= iter <= numIter;
    @ loop invariant getLeft(get_type(protocol)) ==
    @   split_right(getLeft(\at(get_type(protocol),LoopEntry)),iter);
    @ loop invariant getRight(get_type(protocol)) ==
    @   getRight(\at(get_type(protocol),LoopEntry));
    @ loop assigns protocol, iter, u[local_n+1], u[0], u_new[0..local_n-1];
    @ loop variant numIter - iter;
    @*/
  for (iter = 0; iter < numIter; iter++) {
    /*@ ghost
      unroll();
      assoc();
      assoc();
    @*/
    /*@ assert getLeft(get_type(protocol)) == protocol_6;*/
    /*@ assert getLeft(getRight(get_type(protocol))) == protocol_7;*/
    /*@ assert getLeft(getRight(getRight(get_type(protocol)))) ==
                 split_right(getLeft(\at(get_type(protocol),LoopEntry)),iter+1);*/
    /*@ assert getRight(getRight(getRight(get_type(protocol)))) ==
                     getRight(\at(get_type(protocol),LoopEntry));*/

    if (rank == 0) {

      /*@ ghost
          split(procs - 1);
          assoc();
          fsimpl();
          unroll();
          assoc();*/
      MPI_Recv(&u[local_n+1], 1, MPI_INT, right, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      /*@ ghost next();*/
    }
    else if (rank == procs-1) {
      /*@ ghost
          unroll();
          assoc();*/
      MPI_Ssend(&u[1], 1, MPI_INT, left, 0, MPI_COMM_WORLD);
      /*@ ghost fsimpl();*/
    }
    else {
      /*@ ghost
          split(procs-(rank+1));
          assoc();
          fsimpl();
          unroll();
          assoc();*/
      MPI_Recv(&u[local_n+1], 1, MPI_INT, right, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      /*@ ghost
          unroll();
          assoc();*/
      MPI_Ssend(&u[1], 1, MPI_INT, left, 0, MPI_COMM_WORLD);
      /*@ ghost fsimpl();*/
    }
    /*@ assert getLeft(get_type(protocol)) == protocol_7;*/
    /*@ assert getLeft(getRight(get_type(protocol))) ==
                 split_right(getLeft(\at(get_type(protocol),LoopEntry)),iter+1);*/
    /*@ assert getRight(getRight(get_type(protocol))) ==
                     getRight(\at(get_type(protocol),LoopEntry));*/

    if (rank == 0) {
      /*@ ghost
          unroll();
          assoc();*/
      MPI_Ssend(&u[local_n], 1, MPI_INT, right, 0, MPI_COMM_WORLD);
      /*@ ghost fsimpl();*/
    } else if (rank == procs - 1) {
      /*@ ghost
          split(procs - 2);
          assoc();
          fsimpl();
          unroll();
          assoc();*/
      MPI_Recv(&u[0], 1, MPI_INT, left, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      /*@ ghost next();*/
    } else {
      /*@ ghost
          split(rank-1);
          assoc();
          fsimpl();
          unroll();
          assoc();*/
      MPI_Recv(&u[0], 1, MPI_INT, left, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      /*@ ghost
          unroll();
          assoc();*/
      MPI_Ssend(&u[local_n], 1, MPI_INT, right, 0, MPI_COMM_WORLD);
      /*@ ghost fsimpl();*/
    }
    compute(u, u_new, local_n, wstep);
    /*@ assert getLeft(get_type(protocol)) ==
          split_right(getLeft(\at(get_type(protocol),LoopEntry)),iter+1);*/
    /*@ assert  getRight(get_type(protocol)) ==
                     getRight(\at(get_type(protocol),LoopEntry));*/
  }
  /*@ ghost next();*/
  MPI_Finalize();
  return 0;
}

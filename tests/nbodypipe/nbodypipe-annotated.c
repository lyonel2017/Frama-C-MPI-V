/**
 * N-body pipeline program.
 *
 * Adapted from "Using MPI, 2nd Edition", Gropp et al., MIT Press
 *   http://www.mcs.anl.gov/research/projects/mpi/usingmpi/examples-usingmpi/advmsg/nbodypipe_c.html
 *
 * Version: $Id: nbodypipe.c 4638 2015-06-09 14:06:37Z edrdo $
 * ParTypes - http://gloss.di.fc.ul.pt/ParTypes
 */
#include <mpi.h>
#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <string.h>

#define MAX_PARTICLES 1000000
#define NUM_ITER      1000000

void InitParticles( float* part, float* vel, int npart);
float ComputeForces( float* part,  float* other_part, float* vel, int npart);
float ComputeNewPos( float* part, float* pv, int npart, float );



int main(int argc,char** argv) {
  int        rank = 0, procs = 0, npart = 0, left = 0, right = 0, iter, pipe, i;
  float      sim_t, dt, dt_local, max_f, max_f_seg;
  float      particles[MAX_PARTICLES * 4];   /* Particles on ALL nodes */
  float      pv[MAX_PARTICLES * 6];          /* Particle velocity */
  float      sendbuf[MAX_PARTICLES * 4],     /* Pipeline buffers */
             recvbuf[MAX_PARTICLES * 4];

  MPI_Init( &argc, &argv );
  MPI_Comm_rank( MPI_COMM_WORLD, &rank );
  MPI_Comm_size( MPI_COMM_WORLD, &procs );

  left = rank == 0 ? procs - 1 : rank -1;
  right = rank == procs - 1 ?  0 : rank + 1;
  npart = MAX_PARTICLES / procs;
  InitParticles(particles, pv, npart);
  sim_t = 0.0f;

  if (rank == 0) {
    /*@ ghost
      l1:;
      unroll();
      assoc();
      @*/
    MPI_Ssend(sendbuf, npart * 4, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
    /*@ ghost
      int j = 1;
      /@ loop invariant 1 <= j <= procs - 1;
      @ loop invariant getFirst(get_type(protocol)) ==
      @  getNext(split(getFirst(\at(get_type(protocol),l1)),j));
      @ loop invariant getNext(get_type(protocol)) ==
      @  getNext(\at(get_type(protocol),l1));
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
    MPI_Recv(recvbuf, npart * 4, MPI_FLOAT, left,  0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    //@ ghost toskip();
  } else {
    /*@ ghost
      l2:;
      int j = 0;
      /@ loop invariant 0 <= j <= rank - 1;
       @ loop invariant getFirst(get_type(protocol)) ==
       @  getNext(split(getFirst(\at(get_type(protocol),l2)),j));
       @ loop invariant getNext(get_type(protocol)) ==
       @  getNext(\at(get_type(protocol),l2));
       @ loop assigns protocol, j;
       @ loop variant rank - 1 - j;
       @/
      while (j < rank - 1) {
        unroll();
        assoc();
        toskip();
        j++;
      }
      unroll();
      assoc();
      @*/
      MPI_Recv(recvbuf, npart * 4, MPI_FLOAT, left,  0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      //@ ghost j = rank;
      // //@ assert getFirst(get_type(protocol)) == getNext(split(getFirst(\at(get_type(protocol),l2)),j));
      // //@ assert getNext(get_type(protocol)) == getNext(\at(get_type(protocol),l2));
      /*@ ghost
        unroll();
        assoc();
        @*/
      MPI_Ssend(sendbuf, npart * 4, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
      /*@ ghost
        j = rank + 1;
        //@ assert getFirst(get_type(protocol)) == getNext(split(getFirst(\at(get_type(protocol),l2)),j));
        //@ assert getNext(get_type(protocol)) == getNext(\at(get_type(protocol),l2));
        /@ loop invariant rank + 1 <= j <= procs;
         @ loop invariant getFirst(get_type(protocol)) ==
         @  getNext(split(getFirst(\at(get_type(protocol),l2)),j));
         @ loop invariant getNext(get_type(protocol)) ==
         @  getNext(\at(get_type(protocol),l2));
         @ loop assigns protocol, j;
         @ loop variant procs - j;
         @/
        while (j < procs) {
          //@ assert getFirst(get_type(protocol)) == getNext(split(getFirst(\at(get_type(protocol),l2)),j));
          //@ assert getNext(get_type(protocol)) == getNext(\at(get_type(protocol),l2));
          unroll();
          assoc();
          toskip();
          j++;
        }
        toskip();
      @*/
  }
  MPI_Finalize();
  // //@ assert \false;
  return 0;
}


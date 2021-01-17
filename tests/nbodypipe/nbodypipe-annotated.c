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


//@ ensures \initialized(vector + (0..n-1));
void init(float* vector, int n);


void InitParticles( float* part, float* vel, int npart);
float ComputeForces( float* part,  float* other_part, float* vel, int npart);
float ComputeNewPos( float* part, float* pv, int npart, float );

int main(int argc,char** argv) {
  int         rank, procs, npart, left, right, iter, pipe, i;
  float       sim_t, dt, dt_local, max_f, max_f_seg;
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

  init(sendbuf, npart*4);
  //@ assert \initialized(sendbuf + (0..npart*4-1));
  if (rank == 0) {
    MPI_Ssend(sendbuf, npart * 4, MPI_FLOAT, right, 0, MPI_COMM_WORLD);

    /*@ ghost 
      l1:;
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
      toskip();
    @*/
    MPI_Recv(recvbuf, npart * 4, MPI_FLOAT, left,  0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  } 
  else {


    /*@ ghost 
      int j;
      if (rank > 1) {
        toskip();
      }
      l2:;
      if (rank > 1 && rank < procs - 1) {
        j = 1;
        /@ loop invariant 1 <= j <= rank - 1;
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
      }
      l3:;
      if (rank == procs - 1) {
        j = 1;
        /@ loop invariant 1 <= j <= procs-2;
        @ loop invariant getFirst(get_type(protocol)) == 
        @  getNext(split(getFirst(\at(get_type(protocol),l3)),j));
        @ loop invariant getNext(get_type(protocol)) == 
        @  getNext(\at(get_type(protocol),l3));
        @ loop assigns protocol, j; 
        @ loop variant procs - 2 - j; 
        @/
        while (j < procs - 2) {
          unroll();
          assoc();
          toskip();
          j++;
        }
        unroll(); 
        assoc();
      }
      @*/
      MPI_Recv(recvbuf, npart * 4, MPI_FLOAT, left,  0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      /*@ ghost 
        l4:;
        if (rank < procs - 1) {
          unroll(); 
          assoc(); 
        }
        if (rank == procs - 1) {
          toskip();          
        }
        @*/
      MPI_Ssend(sendbuf, npart * 4, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
      /*@ ghost 
      if (rank > 1 && rank < procs - 1) {
        j = rank + 1; 
        /@ loop invariant rank + 1 <= j <= procs - 1;
          @ loop invariant getFirst(get_type(protocol)) == 
          @  getNext(split(getFirst(\at(get_type(protocol),l2)),j));
          @ loop invariant getNext(get_type(protocol)) == 
          @  getNext(\at(get_type(protocol),l2));
          @ loop assigns protocol, j; 
          @ loop variant procs - 1 - j; 
          @/
        while (j < procs - 1) {
          unroll();
          assoc();
          toskip();
          j++;
        }
        toskip(); 
        toskip();
      }

      if (rank == 1) {
        j = rank + 1; 
        /@ loop invariant rank + 1 <= j <= procs - 1;
          @ loop invariant getFirst(get_type(protocol)) == 
          @  getNext(split(getFirst(\at(get_type(protocol),l4)),j));
          @ loop invariant getNext(get_type(protocol)) == 
          @  getNext(\at(get_type(protocol),l4));
          @ loop assigns protocol, j; 
          @ loop variant procs - 1 - j; 
          @/
        while (j < procs - 1) {
          unroll();
          assoc();
          toskip();
          j++;
        }
        toskip(); 
        toskip();        
      }
      @*/
  }
  MPI_Finalize();
  //@ assert \false;
  return 0;
}


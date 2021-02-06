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

//@ assigns \result;
float ComputeForces( float* part,  float* other_part, float* vel, int npart);

//@ assigns \result;
float ComputeNewPos( float* part, float* pv, int npart, float );

/*@ axiomatic MPI_aux_driver {
  @ logic logic_protocol protocol_0;
  @ logic logic_protocol protocol_01;
  @ logic logic_protocol protocol_1;
  @ logic logic_protocol protocol_2;
  @ logic logic_protocol protocol_foo_1(integer i);
  @ }
  @*/

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

  //@ ghost l02:;
  /*@ requires get_type(protocol) == the_protocol;
    @ assigns pipe,protocol,recvbuf[0..npart*4-1],max_f_seg,max_f,iter;
    @ assigns dt_local,sim_t;
    @ ensures isSkip(get_type(protocol));
    @*/
  /*@ loop invariant 1 <= iter <= NUM_ITER+1;
    @ loop invariant iter <= NUM_ITER ==> getFirst(get_type(protocol)) ==
    @   getNext(split(getFirst(\at(get_type(protocol),l02)),iter-1));
    @ loop invariant iter <= NUM_ITER ==> getNext(get_type(protocol)) ==
    @   getNext(\at(get_type(protocol),l02));
    @ loop invariant iter == NUM_ITER+1 ==> get_type(protocol) ==
    @   getNext(\at(get_type(protocol),l02));
    @ loop assigns pipe,protocol,recvbuf[0..npart*4-1],max_f_seg,max_f,iter;
    @ loop assigns dt_local,sim_t;
    @ loop variant NUM_ITER+1-iter;
    @*/
  for (iter = 1; iter <= NUM_ITER; iter++) {
  /*@ ghost
    unroll();
    assoc();
    l01:;
    @*/
    // //@ assert getLeft(get_type(protocol)) == protocol_01;
    // //@ assert getLeft(getLeft(get_type(protocol))) == protocol_0;
    // //@ assert getLeft(getLeft(getLeft(get_type(protocol)))) == protocol_0;
    // //@ assert getRight(getLeft(getLeft(get_type(protocol)))) == protocol_0;
//
    // //@ assert getRight(getLeft(get_type(protocol))) == protocol_2;
    // //@ assert getLeft(getRight(getLeft(get_type(protocol)))) == protocol_2;
    // //@ assert getRight(getRight(getLeft(get_type(protocol)))) == protocol_2;
  /*@ requires getLeft(get_type(protocol)) == protocol_01;
    @ requires getLeft(getLeft(get_type(protocol))) == protocol_0;
    @ requires getRight(getLeft(get_type(protocol))) == protocol_2;
    @ requires getFirst(getNext(get_type(protocol))) == protocol_2;
    @ assigns pipe,protocol,recvbuf[0..npart*4-1],max_f_seg,max_f;
    @ ensures getFirst(get_type(protocol)) == protocol_2;
    @ ensures getFirst(getNext(get_type(protocol))) ==
    @   getNext(split(getFirst(\at(get_type(protocol),l02)),iter));
    @ ensures getNext(getNext(get_type(protocol))) ==
    @   getNext(\at(get_type(protocol),l02));
    @*/
  /*@ loop invariant 1 <= pipe <= procs;
    @ loop invariant pipe < procs ==> getFirst(get_type(protocol)) ==
    @   getNext(split(getFirst(\at(get_type(protocol),l01)),pipe-1));
    @ loop invariant pipe < procs ==> getNext(get_type(protocol)) ==
    @   getNext(\at(get_type(protocol),l01));
    @ loop invariant pipe == procs ==> get_type(protocol) ==
    @   getNext(\at(get_type(protocol),l01));
    @ loop assigns pipe,protocol,recvbuf[0..npart*4-1],max_f_seg,max_f;
    @ loop variant procs-pipe;
    @*/
	for (pipe=1; pipe < procs; pipe++) {
    /*@ ghost
      @ l0:;
      @ unroll();
      @ assoc();
      @*/
    /*@ requires getFirst(get_type(protocol)) == protocol_1;
      @ assigns protocol, recvbuf[0..npart*4-1];
      @ ensures getFirst(get_type(protocol)) ==
      @   getNext(split(getFirst(\at(get_type(protocol),l01)),pipe));
      @ ensures getNext(get_type(protocol)) ==
      @   getNext(\at(get_type(protocol),l01));
      // @ ensures get_type(protocol) ==
      // @   getNext(\at(get_type(protocol),l01));
      @*/
    if (rank == 0) {
      /*@ ghost
        int j = 0;
        l1:;
        unroll();
        assoc();
        @*/
      /*@ requires getFirst(get_type(protocol)) == protocol_foo_1(j);
        @ assigns protocol;
        @ ensures getFirst(get_type(protocol)) ==
        @   getNext(split(getFirst(\at(get_type(protocol),l1)),j+1));
        @ ensures getNext(get_type(protocol)) ==
        @   getNext(\at(get_type(protocol),l1));
        @*/
      MPI_Ssend(sendbuf, npart * 4, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
      /*@ ghost
        j++;
        /@ requires j == 1;
        @ requires getFirst(get_type(protocol)) ==
        @   getNext(split(getFirst(\at(get_type(protocol),l1)),j));
        @ requires getNext(get_type(protocol)) ==
        @   getNext(\at(get_type(protocol),l1));
        @ assigns protocol, j;
        @ ensures j == procs-1;
        @ ensures getFirst(get_type(protocol)) == protocol_foo_1(j);
        @ ensures getFirst(getNext(get_type(protocol))) ==
        @   getNext(split(getFirst(\at(get_type(protocol),l1)),j+1));
        @ ensures getNext(getNext(get_type(protocol))) ==
        @   getNext(\at(get_type(protocol),l1));
        @/
        {
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
            //@ assert getFirst(get_type(protocol)) == protocol_foo_1(j);
            toskip();
            j++;
          }
          unroll();
          assoc();
        }
      @*/
      //@ assert getFirst(get_type(protocol)) == protocol_foo_1(j);
      MPI_Recv(recvbuf, npart * 4, MPI_FLOAT, left,  0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      /*@ ghost
        j++;
        /@ requires j == procs;
         @ requires getFirst(get_type(protocol)) ==
         @   getNext(split(getFirst(\at(get_type(protocol),l1)),j));
         @ assigns protocol;
         @ ensures getFirst(get_type(protocol)) ==
         @   getNext(split(getFirst(\at(get_type(protocol),l01)),pipe));
         @ ensures getNext(get_type(protocol)) ==
         @   getNext(\at(get_type(protocol),l01));
        //  @ ensures get_type(protocol) ==
        //  @   getNext(\at(get_type(protocol),l01));
         @/
         toskip();
         @*/
    } else {
      /*@ ghost
        l2:;
        int j = 0;
        /@ requires j == 0;
        @ requires getFirst(get_type(protocol)) == protocol_1;
        @ assigns protocol,j;
        @ ensures getFirst(get_type(protocol)) == protocol_foo_1(j);
        @ ensures getFirst(getNext(get_type(protocol))) ==
        @   getNext(split(getFirst(\at(get_type(protocol),l2)),j+1));
        @ ensures getNext(getNext(get_type(protocol))) ==
        @   getNext(\at(get_type(protocol),l2));
        @ ensures j == rank-1;
        @/
        {
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
            //@ assert getFirst(get_type(protocol)) == protocol_foo_1(j);
            toskip();
            j++;
          }
          unroll();
          assoc();
        }
        @*/
        //@ assert getFirst(get_type(protocol)) == protocol_foo_1(j);
        MPI_Recv(recvbuf, npart * 4, MPI_FLOAT, left,  0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
        /*@ ghost
          j++;
          unroll();
          assoc();
          @*/
        //@ assert getFirst(get_type(protocol)) == protocol_foo_1(j);
        MPI_Ssend(sendbuf, npart * 4, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
        /*@ ghost
          j++;
          /@ requires j == rank+1;
          @ requires getFirst(get_type(protocol)) ==
          @   getNext(split(getFirst(\at(get_type(protocol),l2)),j));
          @ requires getNext(get_type(protocol)) ==
          @   getNext(\at(get_type(protocol),l2));
          @ assigns protocol, j;
          @ ensures getFirst(get_type(protocol)) ==
          @   getNext(split(getFirst(\at(get_type(protocol),l01)),pipe));
          @ ensures getNext(get_type(protocol)) ==
          @   getNext(\at(get_type(protocol),l01));
          // @ ensures get_type(protocol) ==
          // @   getNext(\at(get_type(protocol),l01));
          @/
          {
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
              //@ assert getFirst(get_type(protocol)) == protocol_foo_1(j);
              toskip();
              j++;
            }
            toskip();
          }
        @*/
    }
    max_f_seg = ComputeForces( particles, recvbuf, pv, npart );
    if (max_f_seg > max_f) max_f = max_f_seg;
    /*@ ghost
      if (pipe == procs-1) {
        /@ assert getFirst(get_type(protocol)) ==
         @   getNext(split(getFirst(\at(get_type(protocol),l01)),pipe));
         @/
        toskip();
      }
      @*/
  }
  dt_local = ComputeNewPos( particles, pv, npart, max_f);
  // //@ assert getFirst(get_type(protocol)) == protocol_2;
  /*@ requires getFirst(get_type(protocol)) == protocol_2;
    @ assigns dt_local, protocol;
    @ ensures getFirst(get_type(protocol)) ==
    @   getNext(split(getFirst(\at(get_type(protocol),l02)),iter));
    @ ensures getNext(get_type(protocol)) ==
    @   getNext(\at(get_type(protocol),l02));
    @*/
  MPI_Allreduce( &dt, &dt_local, 1, MPI_FLOAT, MPI_MIN, MPI_COMM_WORLD);
  sim_t += dt;

  /*@ ghost
      if (iter == NUM_ITER) {
        /@ assert getFirst(get_type(protocol)) ==
         @   getNext(split(getFirst(\at(get_type(protocol),l02)),iter));
         @/
        toskip();
      }
      @*/
  }


  //@ ghost toskip();
  MPI_Finalize();
  // //@ assert \false;
  return 0;
}


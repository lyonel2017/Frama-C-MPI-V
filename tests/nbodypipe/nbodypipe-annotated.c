n/**
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
  @ logic logic_protocol protocol_1;
  @ logic logic_protocol protocol_2;
  @ logic logic_protocol protocol_3;
  @ logic logic_protocol protocol_4;
  @ logic logic_protocol f(integer i);
  @ }
  @*/

//frama-c-gui -mpi-v -wp-driver ../../share/mpi.driver,the_protocol.driver,size.driver nbodypipe.c

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

  /*@ loop invariant 1 <= iter <= NUM_ITER+1;
    @ loop invariant  getFirst(get_type(protocol)) ==
    @   split_right(getFirst(\at(get_type(protocol),LoopEntry)),iter-1);
    @ loop invariant  getNext(get_type(protocol)) ==
    @   getNext(\at(get_type(protocol),LoopEntry));
    @ loop assigns pipe,protocol,recvbuf[0..npart*4-1],max_f_seg,max_f,iter;
    @ loop assigns dt_local,sim_t;
    @ loop variant NUM_ITER+1-iter;
    @*/
  for (iter = 1; iter <= NUM_ITER; iter++) {
  /*@ ghost
     unroll();
     assoc();
     assoc();
    @*/

  /*@ assert getFirst(get_type(protocol)) == protocol_0;*/
  /*@ loop invariant 1 <= pipe <= procs;
    @ loop invariant  getFirst(get_type(protocol)) ==
    @   split_right(getFirst(\at(get_type(protocol),LoopEntry)),pipe-1));
    @ loop invariant  getNext(get_type(protocol)) ==
    @   getNext(\at(get_type(protocol),LoopEntry));
    @ loop assigns pipe,protocol,recvbuf[0..npart*4-1],max_f_seg,max_f;
    @ loop variant procs-pipe;
    @*/
    for (pipe=1; pipe < procs; pipe++) {
    /*@ ghost
       unroll();
       assoc();
       assoc();
      @*/
      /*@ assert getFirst(get_type(protocol)) == protocol_1;*/

    if (rank == 0) {
      /*@ ghost
        l1:;
        unroll();
        assoc();
        @*/

      /*@ assert getFirst(get_type(protocol)) == protocol_foo_1(j);*/

      MPI_Ssend(sendbuf, npart * 4, MPI_FLOAT, right, 0, MPI_COMM_WORLD);

      /*@ ghost
        l2:;
         split(procs - 1);
         assoc();
         fsimpl();
         unroll();
         assoc();*/

      //@ assert getFirst(get_type(protocol)) == protocol_foo_1(j);
      MPI_Recv(recvbuf, npart * 4, MPI_FLOAT, left,  0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      /*@ ghost next();
        @*/
      /*@ assert get_type(protocol) == getNext(\at(get_type(protocol),l1));*/
    } else {

      /*@ ghost
        l1:;
         split(my_rank-1);
         assoc();
         fsimpl();
         unroll();
         assoc();*/

        //@ assert getFirst(get_type(protocol)) == protocol_foo_1(j);
        MPI_Recv(recvbuf, npart * 4, MPI_FLOAT, left,  0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
        /*@ ghost
          j++;*/

	//@ assert getFirst(get_type(protocol)) ==  getNext(split(getFirst(\at(get_type(protocol),l2)),j));
        //@ assert getNext(get_type(protocol)) ==  getNext(\at(get_type(protocol),l2));

	/*@ ghost
          unroll();
          assoc();
          @*/
	//@ assert getFirst(get_type(protocol)) == protocol_foo_1(j);
        MPI_Ssend(sendbuf, npart * 4, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
      /*@ ghost fsimpl();
	@*/
	/*@ assert get_type(protocol) == getNext(\at(get_type(protocol),l2));*/
    }
    max_f_seg = ComputeForces( particles, recvbuf, pv, npart );
    if (max_f_seg > max_f) max_f = max_f_seg;
    }
    /*@ ghost next();
      @ */
    /*@ assert getFirst(get_type(protocol)) == protocol_2;*/

    dt_local = ComputeNewPos( particles, pv, npart, max_f);

    MPI_Allreduce( &dt, &dt_local, 1, MPI_FLOAT, MPI_MIN, MPI_COMM_WORLD);
    sim_t += dt;
  }
  /*@ ghost next();
    @ */

  MPI_Finalize();
  // assert \false;
  return 0;
}

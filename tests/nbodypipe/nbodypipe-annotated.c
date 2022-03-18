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

void InitParticles( int* part, int* vel, int npart);

//@ assigns \result;
int ComputeForces( int* part,  int* other_part, int* vel, int npart);

//@ assigns \result;
int ComputeNewPos( int* part, int* pv, int npart, int );

/*@ axiomatic MPI_aux_driver {
  @ logic logic_protocol protocol_1;
  @ logic logic_protocol protocol_2;
  @ logic logic_protocol protocol_3;
  @ logic logic_protocol protocol_4;
  @ logic logic_protocol f(integer i);
  @ }
  @*/

//frama-c-gui -mpi-v -wp-driver ../../share/mpi.driver,the_protocol.driver,size.driver nbodypipe-annotated.c

int main(int argc,char** argv) {
  int        rank = 0, procs = 0, npart = 0, left = 0, right = 0, iter, pipe, i;
  int      sim_t, dt, dt_local, max_f, max_f_seg;
  int      particles[MAX_PARTICLES * 4];   /* Particles on ALL nodes */
  int      pv[MAX_PARTICLES * 6];          /* Particle velocity */
  int      sendbuf[MAX_PARTICLES * 4],     /* Pipeline buffers */
             recvbuf[MAX_PARTICLES * 4];

  MPI_Init( &argc, &argv );
  MPI_Comm_rank( MPI_COMM_WORLD, &rank );
  MPI_Comm_size( MPI_COMM_WORLD, &procs );

  left = rank == 0 ? procs - 1 : rank -1;
  right = rank == procs - 1 ?  0 : rank + 1;
  npart = MAX_PARTICLES / procs;
  InitParticles(particles, pv, npart);
  sim_t = 0.0f;

  /*@ loop invariant 0 <= iter <= NUM_ITER;
    @ loop invariant getLeft(get_type(protocol)) ==
    @   split_right(\at(get_type(protocol),LoopEntry),iter);
    @ loop invariant isSkip(getRight(get_type(protocol)));
    @ loop assigns pipe,protocol,recvbuf[0..npart*4-1],max_f_seg,max_f,iter;
    @ loop assigns dt_local,sim_t;
    @ loop variant NUM_ITER+1-iter;
    @*/
  for (iter = 0; iter < NUM_ITER; iter++) {
  /*@ ghost
     unroll();
     assoc();
     assoc();
    @*/

  /*@ assert getLeft(get_type(protocol)) == protocol_2;*/
  /*@ loop invariant 1 <= pipe <= procs;
    @ loop invariant getLeft(get_type(protocol)) ==
    @   split_right(getLeft(\at(get_type(protocol),LoopEntry)),pipe);
    @ loop invariant getRight(get_type(protocol)) ==
    @   getRight(\at(get_type(protocol),LoopEntry));
    @ loop assigns pipe,protocol,recvbuf[0..npart*4-1],max_f_seg,max_f;
    @ loop variant procs-pipe;
    @*/
    for (pipe=1; pipe < procs; pipe++) {
      /*@ ghost
          unroll();
          assoc();
        @*/
        /*@ assert getLeft(get_type(protocol)) == protocol_3;*/

      if (rank == 0) {
        /*@ ghost
            unroll();
            assoc();
          @*/

        MPI_Ssend(sendbuf, npart * 4, MPI_INT, right, 0, MPI_COMM_WORLD);

        /*@ ghost
            split(procs - 1);
            assoc();
            fsimpl();
            unroll();
            assoc();*/

         MPI_Recv(recvbuf, npart * 4, MPI_INT, left,  0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
         /*@ ghost next();
           @*/
       } else {

         /*@ ghost
             split(rank-1);
             assoc();
             fsimpl();
             unroll();
             assoc();*/

          MPI_Recv(recvbuf, npart * 4, MPI_INT, left,  0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);

          /*@ ghost
              unroll();
              assoc();
             @*/
          MPI_Ssend(sendbuf, npart * 4, MPI_INT, right, 0, MPI_COMM_WORLD);
         /*@ ghost fsimpl();
           @*/
       }
       max_f_seg = ComputeForces( particles, recvbuf, pv, npart );
       if (max_f_seg > max_f) max_f = max_f_seg;
    }
    /*@ ghost next();
      @ */
    /*@ assert getLeft(get_type(protocol)) == protocol_4;*/

    dt_local = ComputeNewPos( particles, pv, npart, max_f);

    MPI_Allreduce( &dt, &dt_local, 1, MPI_INT, MPI_MIN, MPI_COMM_WORLD);
    sim_t += dt;
  }
  /*@ ghost next();
    @ */

  MPI_Finalize();
  return 0;
}

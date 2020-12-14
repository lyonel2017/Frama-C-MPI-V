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
  for (iter = 1; iter <= NUM_ITER; iter++) {
	for (pipe=1; pipe < procs; pipe++) {
      if (rank == 0) {
        MPI_Send(sendbuf, npart * 4, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
	    MPI_Recv(recvbuf, npart * 4, MPI_FLOAT, left,  0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      } 
      else {
        MPI_Recv(recvbuf, npart * 4, MPI_FLOAT, left,  0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
        MPI_Send(sendbuf, npart * 4, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
      }
      max_f_seg = ComputeForces( particles, recvbuf, pv, npart );
      if (max_f_seg > max_f) max_f = max_f_seg;
	}
	dt_local = ComputeNewPos( particles, pv, npart, max_f);
    MPI_Allreduce( &dt, &dt_local, 1, MPI_FLOAT, MPI_MIN, MPI_COMM_WORLD);
    sim_t += dt;
  }
  MPI_Finalize();
  return 0;
}


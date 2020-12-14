/**
 * N-body pipeline program - annotated version with deliberate error.
 * Search ERROR below for the error location.
 *
 * Adapted from "Using MPI, 2nd Edition", Gropp et al., MIT Press
 *   http://www.mcs.anl.gov/research/projects/mpi/usingmpi/examples-usingmpi/advmsg/nbodypipe_c.html
 *
 * Version: $Id: nbodypipe-with-error-annotated.c 4638 2015-06-09 14:06:37Z edrdo $
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

// Protocol header
#include "nbodypipe.h"

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
  _(assume MAX_PARTICLES % procs == 0)
  _applyInt(MAX_PARTICLES);
  npart = MAX_PARTICLES / procs;
  InitParticles(particles, pv, npart);
  _applyInt(NUM_ITER);

  _(ghost Cons _cfe0 = cons(_protocol, _rank))    
  _(ghost Protocol _fe0 = head(_cfe0))
  _(assert foreachLower(_fe0) == 1)                     
  _(assert foreachUpper(_fe0) == NUM_ITER)   
  _(ghost IntAbs _fe0Body = foreachBody(_fe0))   
  sim_t = 0.0f;
  for (iter = 1; iter <= NUM_ITER; iter++) {
    _(ghost _protocol = _fe0Body[iter])
    _(ghost Cons _cfe1 = cons(_protocol, _rank))    
    _(ghost Protocol _fe1 = head(_cfe1))
    _(assert foreachLower(_fe1) == 1)                     
    _(assert foreachUpper(_fe1) == procs - 1)   
    _(ghost IntAbs _fe1Body = foreachBody(_fe1))
	for (pipe=1; pipe < procs; pipe++) {
	  _(ghost _protocol = _fe1Body[pipe])
      _(ghost Cons _cfe2 = cons(_protocol, _rank))    
      _(ghost Protocol _fe2 = head(_cfe2))
      _(assert foreachLower(_fe2) == 0)         
      _(assert foreachUpper(_fe2) == procs-1)  
      _(ghost IntAbs _feBody2 = foreachBody(_fe2))   
      if (rank == 0) {
        _(ghost _protocol = _feBody2[_rank])
        MPI_Send(sendbuf, npart * 4, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
        _(assert isSkip(_protocol, _rank)) 
        _(ghost _protocol = _feBody2[left])
	    MPI_Recv(recvbuf, npart * 4, MPI_FLOAT, left+1 /* ERROR: should be left */,  
	             0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
	    _(assert isSkip(_protocol, _rank))
        _(assert \forall \integer i; i >= 0 && i < procs && (i != _rank && i != left) 
         ==> isSkip(_feBody2[i], _rank))    
      } 
      else {
        _(ghost _protocol = _feBody2[left])
	      MPI_Recv(recvbuf, npart * 4, MPI_FLOAT, left,  0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
	    _(assert isSkip(_protocol, _rank))      
	    _(ghost _protocol = _feBody2[_rank])
        MPI_Send(sendbuf, npart * 4, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
        _(assert isSkip(_protocol, _rank)) 
        _(assert \forall \integer i; i >= 0 && i < procs && (i != _rank && i != left) 
         ==> isSkip(_feBody2[i], _rank))
      }
      max_f_seg = ComputeForces( particles, recvbuf, pv, npart );
#ifndef _PARTYPES
      if (max_f_seg > max_f) max_f = max_f_seg;
#endif
      _(ghost _protocol = tail(_cfe2))
      _(assert isSkip(_protocol, _rank)) 
	}
	_(ghost _protocol = tail(_cfe1))
#ifndef _PARTYPES
	dt_local = ComputeNewPos( particles, pv, npart, max_f);
#endif
    MPI_Allreduce( &dt, &dt_local, 1, MPI_FLOAT, MPI_MIN, MPI_COMM_WORLD);
#ifndef _PARTYPES
    sim_t += dt;
#endif
    _(assert isSkip(_protocol, _rank))
  }
  _(ghost _protocol = tail(_cfe0))
  MPI_Finalize();
  // Uncomment for sanity check
  // _(assert \false)
  return 0;
}



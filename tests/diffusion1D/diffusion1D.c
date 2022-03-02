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

// External functions
int getNumIterations(void);
int getProblemSize(int procs);
int getWstep();
void getInitialData(int rank, float* data, int len);
int compute(float* u, float* u_new, int len, int wstep);

int main(int argc, char** argv) {
  int procs;  // process count
  int rank; // process rank */
  int n ; // number of discrete points including endpoints
  int local_n; // size of local data = n / procs
  int numIter ; // number of time steps
  int wstep ;  // write frame every this many time steps
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
  MPI_Bcast(&numIter, 1, MPI_INT, 0, MPI_COMM_WORLD);
  MPI_Bcast(&wstep, 1, MPI_INT, 0, MPI_COMM_WORLD);
  local_n = n / procs;
  if (rank == 0) {
    getInitialData(0, &u[1], local_n);
    for (i = 1; i < procs; i++) {
      getInitialData(i, buf, local_n);
      MPI_Send(buf, local_n, MPI_FLOAT, i, 0, MPI_COMM_WORLD);
    }
  } else {
    MPI_Recv(&u[1], local_n, MPI_FLOAT, 0, 0, MPI_COMM_WORLD, &status);
  }
  start = rank == 0 ? 2 : 1;
  stop  = rank == procs - 1 ? n - 1 : n;
  left  = rank - 1;
  right = rank + 1;
  for (iter = 0; iter < numIter; iter++) {
    if (rank == 0) {
      MPI_Recv(&u[local_n+1], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD, &status);
    }
    else if (rank == procs-1) {
      MPI_Send(&u[1], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD);
    }
    else {
      MPI_Recv(&u[local_n+1], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD, &status);
      MPI_Send(&u[1], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD);
    }
    if (rank == 0) {
      MPI_Send(&u[local_n], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
    } else if (rank == procs - 1) {
      MPI_Recv(&u[0], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD, &status);
    } else {
      MPI_Recv(&u[0], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD, &status);
    }
    compute(u, u_new, local_n, wstep);
  }
  MPI_Finalize();
  return 0;
}

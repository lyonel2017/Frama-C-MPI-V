/** 
 * ParTypes - http://gloss.di.fc.ul.pt/ParTypes
 *
 * The 1D- heat diffusion program - annotated version.
 *
 * Adapted from:
 *   FEVS: A Functional Equivalence Verification Suite. 
 *   http://vsl.cis.udel.edu/fevs/index.html
 *   
 * Version: $Id: diffusion1D.prot 4690 2015-06-24 10:18:56Z edrdo $
 */
 
// MPI header
#include <mpi.h>

// Protocol header
#include "diffusion1D.h"

// Program definitions
#define MAXLEN 10000

// External functions
int getNumIterations(void) 
  _(ensures \result > 0);
int getProblemSize(int procs) 
  _(ensures \result > 0 && \result % procs == 0 && \result <= MAXLEN);
int getWstep() 
  _(ensures \result > 0);
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
  _(ghost Cons _pair1 = cons(_protocol, _rank))
  _(ghost Protocol _fe1 = head(_pair1))
  _(assert foreachLower(_fe1) == 1)
  _(assert foreachUpper(_fe1) == procs-1)
  _(ghost IntAbs _fe1Body = foreachBody(_fe1))
  if (rank == 0) {
    getInitialData(0, &u[1], local_n);
    for (i = 1; i < procs; i++) {
      _(ghost _protocol = _fe1Body[i])
      getInitialData(i, buf, local_n);
      MPI_Send(buf, local_n, MPI_FLOAT, i, 0, MPI_COMM_WORLD);
      _(assert isSkip(_protocol, _rank))
    }
  } else { 
    _(ghost _protocol = _fe1Body[_rank])
    MPI_Recv(&u[1], local_n, MPI_FLOAT, 0, 0, MPI_COMM_WORLD, &status);
    _(assert isSkip(_protocol, _rank))
    _(assert \forall \integer i; i >= 0 && i < procs && i != _rank  
         ==> isSkip(_fe1Body[i], _rank))
  }
  _(ghost _protocol = tail(_pair1))
  start = rank == 0 ? 2 : 1;
  stop  = rank == procs - 1 ? n - 1 : n;
  left  = rank - 1;
  right = rank + 1;
  
  _(ghost Cons _pair2 = cons(_protocol, _rank))
  _(ghost Protocol _fe2 = head(_pair2))
  _(assert foreachLower(_fe2) == 1)
  _(assert foreachUpper(_fe2) == numIter)
  _(ghost IntAbs _fe2Body = foreachBody(_fe2))
  for (iter = 0; iter < numIter; iter++) {
    _(ghost _protocol = _fe2Body[iter+1])
    _(ghost Cons _pair3 = cons(_protocol, _rank))
    _(ghost Protocol _fe3 = head(_pair3))
    _(assert foreachLower(_fe3) == 1)
    _(assert foreachUpper(_fe3) == procs - 1)
    _(ghost IntAbs _fe3Body = foreachBody(_fe3))
    if (rank == 0) {
      _(ghost _protocol = _fe3Body[right])
      MPI_Recv(&u[local_n+1], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD, &status);
      _(assert isSkip(_protocol, _rank))
      _(assert \forall \integer i; i > 0 && i < procs && i != right  
        ==> isSkip(_fe3Body[i], _rank))
    } 
    else if (rank == procs-1) { 
      _(ghost _protocol = _fe3Body[_rank])
      MPI_Send(&u[1], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD);
      _(assert isSkip(_protocol, _rank))
      _(assert \forall \integer i; i > 0 && i < procs && i != _rank  
        ==> isSkip(_fe3Body[i], _rank))
    }
    else {
      _(ghost _protocol = _fe3Body[right])
      MPI_Recv(&u[local_n+1], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD, &status);
      _(assert isSkip(_protocol, _rank))
      _(ghost _protocol = _fe3Body[_rank])
      MPI_Send(&u[1], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD);
      _(assert isSkip(_protocol, _rank))
      _(assert \forall \integer i; i > 0 && i < procs && i != right && i != _rank
        ==> isSkip(_fe3Body[i], _rank))
    }
    _(ghost _protocol = tail(_pair3))
    _(ghost Cons _pair4 = cons(_protocol, _rank))
    _(ghost Protocol _fe4 = head(_pair4))
    _(assert foreachLower(_fe4) == 0)
    _(assert foreachUpper(_fe4) == procs - 2)
    _(ghost IntAbs _fe4Body = foreachBody(_fe4))
    if (rank == 0) {
      _(ghost _protocol = _fe4Body[_rank])
      MPI_Send(&u[local_n], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
      _(assert isSkip(_protocol, _rank))
      _(assert \forall \integer i; i >=0 && i < procs-1 && i != _rank
        ==> isSkip(_fe4Body[i], _rank))
    } else if (rank == procs - 1) {
      _(ghost _protocol = _fe4Body[left])
      MPI_Recv(&u[0], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD, &status);
      _(assert isSkip(_protocol, _rank))
      _(assert \forall \integer i; i >=0 && i < procs-1 && i != left
        ==> isSkip(_fe4Body[i], _rank))
    } else {
      _(ghost _protocol = _fe4Body[left])
      MPI_Recv(&u[0], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD, &status);
      _(assert isSkip(_protocol, _rank))
      _(assert \forall \integer i; i >=0 && i < procs-1 && i != _rank && i != left
        ==> isSkip(_fe4Body[i], _rank))      
    }
    compute(u, u_new, local_n, wstep);
    _(ghost _protocol = tail(_pair4))
    _(assert isSkip(_protocol, _rank))
  }
  _(ghost _protocol = tail(_pair2))
  MPI_Finalize();
  // Uncomment the following line for a sanity check.
  // _(assert \false)
  return 0;
}


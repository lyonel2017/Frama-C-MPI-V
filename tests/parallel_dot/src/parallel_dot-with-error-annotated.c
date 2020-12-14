/**
 * Parallel dot product program - annotated version with a deliberate error.
 * Search ERROR below for the error location.
 *
 * Adapted from:
 *   P.S. Pacheco. Parallel Programming with MPI. Morgan Kaufmann, 1997.
 *   parallel_dot1.c example, Chap.5, p.76
 *
 * Version: $Id: parallel_dot-with-error-annotated.c 4635 2015-06-09 14:05:04Z edrdo $
 * ParTypes - http://gloss.di.fc.ul.pt/ParTypes
 */
#include <stdio.h>
#include <mpi.h>

#define MAXLEN 1000000

// Protocol header
#include "parallel_dot.h"

void Scan_vector(float* v, int len) {
#ifndef _PARTYPES
  printf("Enter vector\n");
  int i;
  for (i = 0; i < len; i++)
    scanf("%f", &v[i]);
#endif
}

float  Serial_dot(float *x, float *y, int n) {
#ifndef _PARTYPES
    int    i; 
    float  sum = 0.0f;
    for (i = 0; i < n; i++)
        sum = sum + x[i]*y[i];
    return sum;
#else
	return 0.0f;
#endif
} 


int getProblemSize(int procs) 
#ifdef _PARTYPES
 _(ensures \result > 0 && \result % procs == 0)
;
#else
{
  int n;
  printf("Vector size? ");
  scanf("%d", &n);
  return n; 
}
#endif

int main(int argc, char** argv)
{
  int    procs; // number of processes 
  int    rank;  // process rank 
  int    n;     // problem size (size of vector at each process)
  float  dot, local_dot, remote_dot;
  int    i;
  MPI_Status status;
  float  local_x[MAXLEN];
  float  local_y[MAXLEN];
  float  temp[MAXLEN];

  MPI_Init(&argc, &argv);
  MPI_Comm_size(MPI_COMM_WORLD, &procs);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  
  if (rank == 0) {
    n = getProblemSize(procs) + 1; // ERROR: adding 1 makes n % p != 0 
  }

  MPI_Bcast(&n, 1, MPI_INT, 0, MPI_COMM_WORLD);
 
  _(assume n <= MAXLEN)
  if (rank == 0) {
    Scan_vector (local_x, n);
    _(ghost Cons _cfe = cons(_protocol, _rank))    
    _(ghost Protocol _fe = head(_cfe))
    _(assert foreachLower(_fe) == 1)                     
    _(assert foreachUpper(_fe) == procs - 1) 
    _(ghost IntAbs _feBody = foreachBody(_fe))   
    for (i=1; i < procs; i++) {
      _(ghost _protocol = _feBody[i])
      Scan_vector (temp, n);
      MPI_Send(temp, n/procs, MPI_FLOAT, i, 0, MPI_COMM_WORLD);
      _(assert isSkip(_protocol, _rank))
    }
    _(ghost _protocol = tail(_cfe))
  } 
  else {
    _(ghost Cons _cfe = cons(_protocol, _rank))    
    _(ghost Protocol _fe = head(_cfe))
    _(ghost IntAbs _feBody = foreachBody(_fe))   
    _(ghost _protocol = _feBody[_rank])
    MPI_Recv(local_x, n/procs, MPI_FLOAT, 0, 0, MPI_COMM_WORLD, &status);
    _(assert isSkip(_protocol, _rank))
    _(assert \forall \integer i; i >= 0 && i < procs && i != _rank
         ==> isSkip(_feBody[i], _rank))     
    _(ghost _protocol = tail(_cfe))
  }
  if (rank == 0) {
    Scan_vector (local_y, n);
    _(ghost Cons _cfe = cons(_protocol, _rank))    
    _(ghost Protocol _fe = head(_cfe))
    _(assert foreachLower(_fe) == 1)                     
    _(assert foreachUpper(_fe) == procs - 1) 
    _(ghost IntAbs _feBody = foreachBody(_fe))   
    for (i=1; i < procs; i++) {
      _(ghost _protocol = _feBody[i])
      Scan_vector (temp, n);
      MPI_Send(temp, n/procs, MPI_FLOAT, i, 0, MPI_COMM_WORLD);
      _(assert isSkip(_protocol, _rank))
    }
    _(ghost _protocol = tail(_cfe))
  } else {
    _(ghost Cons _cfe = cons(_protocol, _rank))    
    _(ghost Protocol _fe = head(_cfe))
    _(ghost IntAbs _feBody = foreachBody(_fe))   
    _(ghost _protocol = _feBody[_rank])
    MPI_Recv(local_y, n/procs, MPI_FLOAT, 0, 0, MPI_COMM_WORLD, &status);
    _(assert isSkip(_protocol, _rank))
    _(assert \forall \integer i; i >= 0 && i < procs && i != _rank
         ==> isSkip(_feBody[i], _rank))     
    _(ghost _protocol = tail(_cfe))
  }
  // Local computation followed by reduction
  local_dot = Serial_dot(local_x, local_y, n);
  MPI_Allreduce(&local_dot, &dot, 1, MPI_FLOAT, MPI_SUM, MPI_COMM_WORLD);
  
  // Print result
#ifndef _PARTYPES
  printf("Result: %f\n", dot);
#endif
  // Print results for each process
  if (rank == 0) {
    _(ghost Cons _cfe = cons(_protocol, _rank))    
    _(ghost Protocol _fe = head(_cfe))
    _(assert foreachLower(_fe) == 1)                     
    _(assert foreachUpper(_fe) == procs - 1) 
    _(ghost IntAbs _feBody = foreachBody(_fe))   
    for (i=1; i < procs; i++) {
      _(ghost _protocol = _feBody[i])
      MPI_Recv(&remote_dot, 1, MPI_FLOAT, i, 0, MPI_COMM_WORLD, &status);
#ifndef _PARTYPES
      printf("Result at process %d : %f\n", i, remote_dot);
#endif
      _(assert isSkip(_protocol, _rank))
    }
    _(ghost _protocol = tail(_cfe))
  } else {
    _(ghost Cons _cfe = cons(_protocol, _rank))    
    _(ghost Protocol _fe = head(_cfe))
    _(ghost IntAbs _feBody = foreachBody(_fe))   
    _(ghost _protocol = _feBody[_rank])
    MPI_Send(&local_dot, 1, MPI_FLOAT, 0, 0, MPI_COMM_WORLD);
    _(assert isSkip(_protocol, _rank))
      _(assert \forall \integer i; i >= 0 && i < procs && i != _rank
         ==> isSkip(_feBody[i], _rank))     
    _(ghost _protocol = tail(_cfe))
  }
  MPI_Finalize();
  // Uncomment for sanity check: _(assert \false)
  return 0;
}
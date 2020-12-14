/** 
 * The finite differences program - annotated version with a deliberate error.
 * Takes a vector X0 and calculates Xn iteratively.
 * Search ERROR below for the error location.
 * 
 * Original algorithm and MPI program:
 * I. Foster. Designing and building Parallel programs. Addison-Wesley, 1995
 *   http://www.mcs.anl.gov/~itf/dbpp/text/node10.html#SECTION02240000000000000000
 *   http://www.mcs.anl.gov/~itf/dbpp/text/node97.html#figmpreduce
 *
 * Version: $Id: fdiff-with-error-annotated.c 4644 2015-06-09 14:55:33Z edrdo $
 * ParTypes - http://gloss.di.fc.ul.pt/ParTypes
 */
#include <mpi.h>
#include "fdiff.h"
#define NUM_ITER 1000000
#define MAX_SIZE 1000000

// External functions
int read_array(float* data, int n);
int write_array(float* data, int n);
void compute(float* data, int n);

int read_problem_size(int procs) 
  _(ensures \result > 0 && \result <= MAX_SIZE && \result % procs == 0)
; 

int main(int argc,char** argv) {
  int procs;             
  int rank;      
  int iter;
  int left, right;
  int n;
  float data[MAX_SIZE+2];                
  float local[MAX_SIZE+2]; 
  float localErr, globalErr; 
  
  MPI_Init(&argc,&argv);
  MPI_Comm_rank(MPI_COMM_WORLD,&rank);
  MPI_Comm_size(MPI_COMM_WORLD,&procs);
  _applyInt(NUM_ITER);
  if (rank == 0)  {
    n = read_problem_size(procs);
    read_array(data, n);
  }
  MPI_Bcast(&n,1,MPI_INT,0,MPI_COMM_WORLD);
  _(assume n <= MAX_SIZE)
  int local_n = n/procs;
  MPI_Scatter(data, local_n, MPI_FLOAT, &local[1], local_n, MPI_FLOAT, 0, MPI_COMM_WORLD);
  left = rank == 0 ? procs - 1 : rank - 1;
  right = rank == procs - 1 ? 0 : rank + 2; // ERROR: rank + 2 in place of rank + 1
  _(ghost Cons _cfe0 = cons(_protocol, _rank))    
  _(ghost Protocol _fe0 = head(_cfe0))
  _(assert foreachLower(_fe0) == 1)                     
  _(assert foreachUpper(_fe0) == NUM_ITER)   
  _(ghost IntAbs _fe0Body = foreachBody(_fe0))   
  for (iter=1; iter <= NUM_ITER; iter++) {
    _(ghost _protocol = _fe0Body[iter])
    _(ghost Cons _cfe1 = cons(_protocol, _rank))    
    _(ghost Protocol _fe1 = head(_cfe1))
    _(assert foreachLower(_fe1) == 0)         
    _(assert foreachUpper(_fe1) == procs-1)  
    _(ghost IntAbs _feBody1 = foreachBody(_fe1))    
    if (rank == 0) {
      _(ghost _protocol = _feBody1[rank])
      MPI_Send(&local[1], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD);
      MPI_Send(&local[n/procs], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
      _(assert isSkip(_protocol,_rank))  
      _(ghost _protocol = _feBody1[right])
      MPI_Recv(&local[n/procs+1], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD, &status);
      _(assert isSkip(_protocol,_rank))  
      _(ghost _protocol = _feBody1[left])
      MPI_Recv(&local[0], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD, &status);
      _(assert isSkip(_protocol,_rank)) 
      _(assert \forall \integer i; i >= 0 && i < procs && (i != _rank && i != left && i != right) 
         ==> isSkip(_feBody1[i], _rank))
     }
     else if (rank == procs - 1) {
      _(ghost _protocol = _feBody1[right])
      MPI_Recv(&local[n/procs+1], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD, &status);
      _(assert isSkip(_protocol,_rank))  
      _(ghost _protocol = _feBody1[left])
      MPI_Recv(&local[0], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD, &status);
      _(assert isSkip(_protocol,_rank)) 
      _(ghost _protocol = _feBody1[rank])
      MPI_Send(&local[1], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD);
      MPI_Send(&local[n/procs], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
      _(assert isSkip(_protocol,_rank))  
      _(assert \forall \integer i; i >= 0 && i < procs && (i != _rank && i != left && i != right) 
         ==> isSkip(_feBody1[i], _rank))
     }
     else {
      _(ghost _protocol = _feBody1[left])
      MPI_Recv(&local[0], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD, &status);
      _(assert isSkip(_protocol,_rank)) 
       _(ghost _protocol = _feBody1[rank])
      MPI_Send(&local[1], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD);
      MPI_Send(&local[n/procs], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
      _(assert isSkip(_protocol,_rank))  
      _(ghost _protocol = _feBody1[right])
      MPI_Recv(&local[n/procs+1], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD, &status);
      _(assert isSkip(_protocol,_rank))  
      _(assert \forall \integer i; i >= 0 && i < procs && (i != _rank && i != left && i != right) 
         ==> isSkip(_feBody1[i], _rank))     
     }
     _(ghost _protocol = tail(_cfe1))
     compute(data, n/procs);
     _(assert isSkip(_protocol,_rank))  
  }
  _(ghost _protocol = tail(_cfe0))
  MPI_Reduce(&localErr,&globalErr,1,MPI_FLOAT,MPI_MAX,0,MPI_COMM_WORLD);
  write_array(data, n);
  MPI_Gather(&local[1],n/procs,MPI_FLOAT,data,n/procs,MPI_FLOAT,0,MPI_COMM_WORLD);
  MPI_Finalize();
}
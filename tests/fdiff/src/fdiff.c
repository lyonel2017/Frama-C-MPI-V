/** 
 * The finite differences program.
 * Takes a vector X0 and calculates Xn iteratively.
 * 
 * Original algorithm and MPI program:
 * I. Foster. Designing and building Parallel programs. Addison-Wesley, 1995
 *   http://www.mcs.anl.gov/~itf/dbpp/text/node10.html#SECTION02240000000000000000
 *   http://www.mcs.anl.gov/~itf/dbpp/text/node97.html#figmpreduce
 *
 * Version: $Id: fdiff.c 4644 2015-06-09 14:55:33Z edrdo $
 * ParTypes - http://gloss.di.fc.ul.pt/ParTypes
 */
#include <mpi.h>
#define NUM_ITER 1000000
#define MAX_SIZE 1000000

// External functions
int read_array(float* data, int n);
int write_array(float* data, int n);
void compute(float* data, int n);

int read_problem_size(int procs); 

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
  if (rank == 0)  {
    n = read_problem_size(procs);
    read_array(data, n);
  }
  MPI_Bcast(&n,1,MPI_INT,0,MPI_COMM_WORLD);
  int local_n = n/procs;
  MPI_Scatter(data, local_n, MPI_FLOAT, &local[1], local_n, MPI_FLOAT, 0, MPI_COMM_WORLD);
  left = rank == 0 ? procs - 1 : rank - 1;
  right = rank == procs - 1 ? 0 : rank + 1;
  for (iter = 1; iter <= NUM_ITER; iter++)  {
    int i;
    if (rank == 0) {
      MPI_Send(&local[1], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD);
      MPI_Send(&local[n/procs], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
      MPI_Recv(&local[n/procs+1], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD, &status);
      MPI_Recv(&local[0], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD, &status);
    } else if (rank == procs-1) {
      MPI_Recv(&local[n/procs+1], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD, &status);
      MPI_Recv(&local[0], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD, &status);
      MPI_Send(&local[1], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD);
      MPI_Send(&local[n/procs], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
    } else {
      MPI_Recv(&local[0], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD, &status);
      MPI_Send(&local[1], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD);
      MPI_Send(&local[n/procs], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
      MPI_Recv(&local[n/procs+1], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD, &status);
    }
    compute(data, n/procs);
  }
  MPI_Reduce(&localErr,&globalErr,1,MPI_FLOAT,MPI_MAX,0,MPI_COMM_WORLD);
  write_array(data, n);
  MPI_Gather(&local[1],n/procs,MPI_FLOAT,data,n/procs,MPI_FLOAT,0,MPI_COMM_WORLD);
  MPI_Finalize();
}
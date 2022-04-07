/**
 * Parallel dot product program.
 *
 * Adapted from:
 *   P.S. Pacheco. Parallel Programming with MPI. Morgan Kaufmann, 1997.
 *   parallel_dot1.c example, Chap.5, p.76
 *s
 * Version: $Id: parallel_dot.c 4635 2015-06-09 14:05:04Z edrdo $
 * ParTypes - http://gloss.di.fc.ul.pt/ParTypes
 */
#include <stdio.h>
#include <mpi.h>

#define MAXLEN 1000000

void Scan_vector(float* v, int len) {
  printf("Enter vector:\n");
  int i;
  for (i = 0; i < len; i++)
    scanf("%f", &v[i]);
}

float  Serial_dot(float *x, float *y, int n) {
    int    i;
    float  sum = 0.0f;
    for (i = 0; i < n; i++)
        sum = sum + x[i]*y[i];
    return sum;
}


int getProblemSize(int procs)
{
  int n;
  printf("Vector size? ");
  scanf("%d", &n);
  return n;
}

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
    n = getProblemSize(procs);
  }

  MPI_Bcast(&n, 1, MPI_INT, 0, MPI_COMM_WORLD);

  if (rank == 0) {
    Scan_vector (local_x, n);
    for (i = 1; i < procs; i++) {
      Scan_vector (temp, n);
      MPI_Send(temp, n, MPI_FLOAT, i, 0, MPI_COMM_WORLD);
    }
  }
  else {
    MPI_Recv(local_x, n, MPI_FLOAT, 0, 0, MPI_COMM_WORLD, &status);
  }

  if (rank == 0) {
    Scan_vector (local_y, n);
    for(i = 1; i < procs; i++) {
      Scan_vector (temp, n);
      MPI_Send(temp, n, MPI_FLOAT, i, 0, MPI_COMM_WORLD);
    }
  }
  else {
    MPI_Recv(local_y, n, MPI_FLOAT, 0, 0, MPI_COMM_WORLD, &status);
  }
  // Local computation followed by reduction
  local_dot = Serial_dot(local_x, local_y, n);
  MPI_Allreduce(&local_dot, &dot, 1, MPI_FLOAT, MPI_SUM, MPI_COMM_WORLD);

  // Print result
  printf("Result: %f\n", dot);

  // Print local at each process
  if (rank == 0) {
    for (i = 1; i < procs; i++) {
      MPI_Recv(&remote_dot, 1, MPI_FLOAT, i, 0, MPI_COMM_WORLD, &status);
      printf("Result at process %d : %f\n", i, remote_dot);
    }
  }
  else {
    MPI_Send(&local_dot, 1, MPI_FLOAT, 0, 0, MPI_COMM_WORLD);
  }
  MPI_Finalize();
  return 0;
}

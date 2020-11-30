/**
 * Pi program - annotated version with a deliberate error.
 * Search ERROR below for the error location.
 *
 * Adapted from:
 *   William Gropp, Ewing Lusk, and Anthony Skjellum. Using MPI (2nd Ed.): 
 *   Portable Parallel Programming with the Message-passing Interface. MIT Press,1999
 *   http://www.mcs.anl.gov/research/projects/mpi/usingmpi/examples-usingmpi/simplempi/cpi_c.html
 *
 * Version: $Id: pi-with-error-annotated.c 4635 2015-06-09 14:05:04Z edrdo $
 * ParTypes - http://gloss.di.fc.ul.pt/ParTypes
 */
#include <stdio.h>
#include <mpi.h>
#include <math.h>
#include "pi.h" // Protocol header

int main(int argc, char **argv)
{
  int n, myid, numprocs, i;
  float PI25DT = 3.141592653589793238462643f;
  float mypi, pi, h, sum, x;
  MPI_Init(&argc,&argv);
  MPI_Comm_size(MPI_COMM_WORLD, &numprocs);
  MPI_Comm_rank(MPI_COMM_WORLD, &myid);
  if (myid == 0) {
    #ifndef _PARTYPES
      printf("Enter the number of intervals: ");
      scanf("%d",&n);
    #endif
  }
  // ERROR: 1 should be the broadcast operation root process, not 0.
  MPI_Bcast(&n, 1, MPI_INT, 1 /* correct: 0 */, MPI_COMM_WORLD);
#ifndef _PARTYPES
  h   = 1.0f / (float) n;
  sum = 0.0f;
  for (i = myid + 1; i <= n; i += numprocs) {
     x = h * ((float)i - 0.5f);
     sum += (4.0f / (1.0f + x*x));
  }
  mypi = h * sum;
#endif
  MPI_Reduce(&mypi, &pi, 1, MPI_FLOAT, MPI_SUM, 0, MPI_COMM_WORLD);
  if (myid == 0) {
#ifndef _PARTYPES
     printf("pi is approximately %.16f, Error is %.16f\n", pi, fabs(pi - PI25DT));
#endif
  } 
  // Uncomment for sanity check:
  // _(assert \false)
  MPI_Finalize();
  return 0;
}

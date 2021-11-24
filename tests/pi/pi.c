/**
 * Pi program.
 *
 * Adapted from:
 *   William Gropp, Ewing Lusk, and Anthony Skjellum. Using MPI (2nd Ed.):
 *   Portable Parallel Programming with the Message-passing Interface. MIT Press,1999
 *   http://www.mcs.anl.gov/research/projects/mpi/usingmpi/examples-usingmpi/simplempi/cpi_c.html
 *
 * Version: $Id: pi.c 4635 2015-06-09 14:05:04Z edrdo $
 * ParTypes - http://gloss.di.fc.ul.pt/ParTypes
 */
#include <stdio.h>
#include <mpi.h>
#include <math.h>

/*@ ensures \result > 0;
  @ assigns \result;*/
int get_n (void);
      // printf("Enter the number of intervals: ");
      // scanf("%d",&n);


/*@ assigns \nothing;*/
void do_pi(float pi, float PI25DT);
    //  printf("pi is approximately %.16f, Error is %.16f\n", pi, fabs(pi - PI25DT));

//frama-c-gui -mpi-v -wp-driver ../../share/mpi.driver,the_protocol.driver,size.driver pi.c

int main(int argc, char **argv)
{
  int n = 0, myid = 0, numprocs = 0, i = 0;
  float PI25DT = 3.141592653589793238462643f;
  float mypi, pi, h, sum, x;
  MPI_Init(&argc,&argv);
  MPI_Comm_size(MPI_COMM_WORLD, &numprocs);
  MPI_Comm_rank(MPI_COMM_WORLD, &myid);
  if (myid == 0) {
    n = get_n();;
  }
  MPI_Bcast(&n, 1, MPI_INT, 0, MPI_COMM_WORLD);
  /*@ assert n > 0;*/
  //@ ghost toskip();
  h   = 1.0f / (float) n;
  sum = 0.0f;
  /*@
    loop invariant 1 <= i <= n + numprocs + 1;
    loop assigns sum, x, i;
    loop variant n - i;
  */
  for (i = myid + 1; i <= n; i += numprocs) {
     x = h * ((float)i - 0.5f);
     sum += (4.0f / (1.0f + x*x));
  }
  mypi = h * sum;

  MPI_Reduce(&mypi, &pi, 1, MPI_FLOAT, MPI_SUM, 0, MPI_COMM_WORLD);

  if (myid == 0) {
    do_pi(pi,PI25DT);
  }
  MPI_Finalize();
  // assert \false;
  return 0;
}

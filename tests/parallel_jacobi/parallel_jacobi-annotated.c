/**
 * Parallel jacobi iteration program -- annotated version.
 *
 * Adapted from:
 *  "Parallel Programming with MPI" by Peter Pacheco, Morgan Kaufmann, 1997.
 *   parallel_jacobi.c example, Chap. 10, p. 220
 *
 * Version: $Id: parallel_jacobi.c 4645 2015-06-09 14:57:16Z edrdo $
 * ParTypes - http://gloss.di.fc.ul.pt/ParTypes
 */
#include <stdio.h>
#include <stdlib.h>
#include <mpi.h>
#include <math.h>


#define MAX_DIM  10000
#define NUM_ITER 1000000

#define MATRIX_DECL(var) float var[MAX_DIM * MAX_DIM]

// External functions

/*@ ensures \valid(matrix + (0..dim-1));
  @ assigns matrix[0..dim-1];*/
void readMatrix(float* matrix, int dim);

/*@ ensures \valid(vector + (0..dim-1));
  @ assigns vector[0..dim-1];*/
void readVector(float* vector, int dim);

void printVector(float* vector, int dim);

/*@ ensures \valid(x_local + (0..n/p-1));
  @ assigns x_local[0..n/p-1];*/
void Jacobi_iteration(float* A_local, float* x_local, float* b_local, float* x_old, int n, int p);


/*@ axiomatic MPI_aux_driver{
  @ logic logic_protocol protocol_1;
  @ logic logic_protocol protocol_2;
  @ logic logic_protocol protocol_3;
  @ logic logic_protocol protocol_4;
  @ logic logic_protocol protocol_while_0;
}*/

//frama-c-gui -mpi-v -wp-driver ../../share/mpi.driver,the_protocol.driver,size.driver parallel_jacobi-annotated.c

int main( int argc, char** argv){

    int    p;
    int    rank;
    int    n;
    int    n_by_p;
    int    iter;
    int    converged;

    float  A_initial[MAX_DIM * MAX_DIM];
    float  A_local[MAX_DIM * MAX_DIM];
    float  b_initial[MAX_DIM];
    float  b_local[MAX_DIM];
    float  x_local[MAX_DIM];
    float  x_temp1[MAX_DIM];
    float  x_temp2[MAX_DIM];
    float  x_final[MAX_DIM];
    float* x_old;
    float* x_new;
    float* tmp;

    MPI_Init(&argc, &argv);
    MPI_Comm_size(MPI_COMM_WORLD, &p);
    MPI_Comm_rank(MPI_COMM_WORLD, &rank);

    n = MAX_DIM;
    n_by_p = n / p;
    if (rank == 0) {
      readMatrix(A_initial, n);
      readVector(b_initial, n);
    }
    MPI_Scatter(A_initial, n_by_p * n, MPI_FLOAT, A_local, n_by_p * n , MPI_FLOAT, 0, MPI_COMM_WORLD);
    MPI_Scatter(b_initial, n_by_p, MPI_FLOAT, x_local, n_by_p, MPI_FLOAT, 0, MPI_COMM_WORLD);
    MPI_Allgather(b_local, n_by_p, MPI_FLOAT, x_temp1, n_by_p, MPI_FLOAT, MPI_COMM_WORLD);

    /*@ assert get_type(protocol) == protocol_3;*/

    x_new = x_temp1;
    x_old = x_temp1;

    /*@ loop invariant 1 <= iter <= NUM_ITER+1;
      @ loop invariant getLeft(get_type(protocol)) ==
      @  split_right (getLeft(\at(get_type(protocol),LoopEntry)),iter);
      @ loop invariant getRight(get_type(protocol)) ==
      @  getRight(\at(get_type(protocol),LoopEntry));
      @ loop invariant \valid(x_old + (0..n_by_p*p-1));
      @ loop invariant \valid(x_new + (0..n_by_p*p-1));
      @ loop invariant \valid(x_local + (0..n_by_p-1));
      @ loop assigns protocol, iter,tmp, x_old, x_new, x_local[0..n_by_p-1];
      @ loop variant NUM_ITER - iter;*/
    for (iter = 1; iter <= NUM_ITER; iter++){
      Jacobi_iteration(A_local, x_local, b_local, x_old, n, p);

      //@ ghost unroll();
      //@ ghost assoc();
      //@ assert getLeft(get_type(protocol)) == protocol_while_0;
      MPI_Allgather(x_local, n_by_p, MPI_FLOAT, x_new, n_by_p, MPI_FLOAT, MPI_COMM_WORLD);
      tmp = x_old;
      x_old = x_new;
      x_new = tmp;
    }

    /*@ ghost next();
      @*/

    /*@ assert get_type(protocol) == protocol_4;*/

    /*@ assert \valid(x_new + (0..n_by_p*p-1));*/

    MPI_Gather(x_new, n_by_p, MPI_FLOAT, x_final, n_by_p, MPI_FLOAT, 0, MPI_COMM_WORLD);

    if (rank == 0) {
      printVector(x_new, n);
    }

    MPI_Finalize();

}

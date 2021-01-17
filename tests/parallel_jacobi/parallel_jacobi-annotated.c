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

//@ ensures \initialized(matrix + (0..dim*dim-1));
void readMatrix(float* matrix, int dim);

/*@ ensures \initialized(vector + (0..dim-1));
  @ ensures \valid(vector + (0..dim-1));
  @*/
void readVector(float* vector, int dim);
void printVector(float* vector, int dim);

/*@ assigns x_local[0..n/p-1];
  @ ensures \initialized(x_local + (0..n/p-1));
  @ ensures \valid(x_local + (0..n/p-1));
  @*/
void Jacobi_iteration(float* A_local, float* x_local, float* b_local, float* x_old, int n, int p);


/**
 * HELPER:
 * for most applications this function can be left out
 * if the receive buffers are initialized after MPI operations
 * */
/*@ ensures \initialized(vector + (0..n-1));
  @ ensures \valid(vector + (0..n-1));
  @ assigns \nothing;
  @*/
void init(float* vector, int n);


/**
 * requires timeout = 90, process = 32
 * tested with wp-fix
 **/
int main( int argc, char** argv){
    // CHANGED: MAX_DIM s.t. MAX_DIM * MAX_DIM can be int
    int        p;
    int        rank;
    int        n;
    int        n_by_p;
    int        iter;
    int        converged;
    // CHANGED: declaration without #define
    float      A_initial[MAX_DIM * MAX_DIM];
    float      A_local[MAX_DIM * MAX_DIM];

    float      b_initial[MAX_DIM];
    float      x_local[MAX_DIM];
    float      b_local[MAX_DIM];
    float   x_temp1[MAX_DIM];
    float   x_temp2[MAX_DIM];
    float   x_final[MAX_DIM];
    float*  x_old;
    float*  x_new;
    float*  tmp;

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
    init(A_local, n_by_p*n);

    MPI_Scatter(b_initial, n_by_p, MPI_FLOAT, x_local, n_by_p, MPI_FLOAT, 0, MPI_COMM_WORLD);
    init(x_local, n_by_p);
    //@ assert \initialized(x_local + (0..n_by_p-1));
    //@ assert \valid(x_local + (0..n_by_p-1));

    init(b_local, n_by_p);
    //@ assert \initialized(b_local + (0..n_by_p-1));
    //@ assert \valid(b_local + (0..n_by_p-1));
    MPI_Allgather(b_local, n_by_p, MPI_FLOAT, x_temp1, n_by_p, MPI_FLOAT, MPI_COMM_WORLD);
    init(x_temp1, n_by_p*p);
    //@ assert \initialized(x_temp1 + (0..n_by_p*p-1));
    //@ assert \valid(x_temp1 + (0..n_by_p*p-1));

    x_new = x_temp1;
    //@ assert \initialized(x_new + (0..n_by_p*p-1));
    //@ assert \valid(x_new + (0..n_by_p*p-1));
    x_old = x_temp1;
    //@ assert \initialized(x_old + (0..n_by_p*p-1));
    //@ assert \valid(x_old + (0..n_by_p*p-1));

    // ADDED: necessary for loop invariant
    tmp = x_temp1;
    //@ assert \initialized(tmp + (0..n_by_p*p-1));
    //@ assert \valid(tmp + (0..n_by_p*p-1));

    /*@ loop invariant 0 <= iter <= NUM_ITER;
      @ loop invariant getFirst(get_type(protocol)) ==
      @  getNext(split (getFirst(\at(get_type(protocol),LoopEntry)),iter));
      @ loop invariant getNext(get_type(protocol)) ==
      @    getNext(\at(get_type(protocol),LoopEntry));
      @ loop invariant \initialized(x_old + (0..n_by_p*p-1));
      @ loop invariant \initialized(x_new + (0..n_by_p*p-1));
      @ loop invariant \initialized(tmp + (0..n_by_p*p-1));
      @ loop invariant \initialized(x_local + (0..n_by_p-1));
      @ loop invariant \valid(x_old + (0..n_by_p*p-1));
      @ loop invariant \valid(x_new + (0..n_by_p*p-1));
      @ loop invariant \valid(tmp + (0..n_by_p*p-1));
      @ loop invariant \valid(x_local + (0..n_by_p-1));
      @ loop assigns protocol, iter,tmp, x_old, x_new, x_local[0..n_by_p-1];
      @ loop variant NUM_ITER - iter;
      @*/
    // CHANGED: starts at 0 instead of 1, end changed respectively
    //          necessary s.t. while can be used in protocol
    for (iter = 0; iter < NUM_ITER; iter++){
      //@ assert \initialized(x_old + (0..n_by_p*p-1));
      //@ assert \initialized(x_new + (0..n_by_p*p-1));
      //@ assert \initialized(tmp + (0..n_by_p*p-1));
      //@ assert \valid(x_old + (0..n_by_p*p-1));
      //@ assert \valid(x_new + (0..n_by_p*p-1));
      //@ assert \valid(tmp + (0..n_by_p*p-1));

      Jacobi_iteration(A_local, x_local, b_local, x_old, n, p);
      //@ assert \initialized(x_local + (0..n_by_p-1));
      //@ assert \valid(x_local + (0..n_by_p-1));

      //@ ghost unroll();
      //@ ghost assoc();
      MPI_Allgather(x_local, n_by_p, MPI_FLOAT, x_new, n_by_p, MPI_FLOAT, MPI_COMM_WORLD);
      init(x_new, n_by_p);
      //@ assert \initialized(x_new + (0..n_by_p*p-1));
      //@ assert \valid(x_new + (0..n_by_p*p-1));

      tmp = x_old;
      //@ assert \initialized(tmp + (0..n_by_p*p-1));
      //@ assert \valid(tmp + (0..n_by_p*p-1));
      x_old = x_new;
      //@ assert \initialized(x_old + (0..n_by_p*p-1));
      //@ assert \valid(x_old + (0..n_by_p*p-1));
      x_new = tmp;
      //@ assert \initialized(x_new + (0..n_by_p*p-1));
      //@ assert \valid(x_new + (0..n_by_p*p-1));
    }
    //@ ghost toskip();
    MPI_Gather(x_new, n_by_p, MPI_FLOAT, x_final, n_by_p, MPI_FLOAT, 0, MPI_COMM_WORLD);

    // REMOVED: no I/O
    // if (rank == 0) {
    //   printVector(x_new, n);
    // }

    MPI_Finalize();
    //@ assert \false;
}

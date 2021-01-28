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

/*@ requires \valid(vector + (0..dim-1));
  @ assigns \nothing;*/
void printVector(float* vector, int dim);

/*@ ensures \valid(x_local + (0..n/p-1));
  @ assigns x_local[0..n/p-1];*/
void Jacobi_iteration(float* A_local, float* x_local, float* b_local, float* x_old, int n, int p);


/*@ axiomatic MPI_aux_driver{
  @ logic logic_protocol protocol_1;
  @ logic logic_protocol protocol_2;
  @ logic logic_protocol protocol_3;
  @ logic logic_protocol protocol_4;
}*/


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
    /*@ requires get_type(protocol) == the_protocol;
      @ assigns protocol, A_local[0..n_by_p*n-1];
      @ ensures get_type(protocol) == protocol_1;*/
    MPI_Scatter(A_initial, n_by_p * n, MPI_FLOAT, A_local, n_by_p * n , MPI_FLOAT, 0, MPI_COMM_WORLD);

    /*@ requires get_type(protocol) == protocol_1;
      @ assigns protocol, x_local[0..n_by_p-1];
      @ ensures get_type(protocol) == protocol_2;*/
    MPI_Scatter(b_initial, n_by_p, MPI_FLOAT, x_local, n_by_p, MPI_FLOAT, 0, MPI_COMM_WORLD);

    /*@ requires get_type(protocol) == protocol_2;
      @ assigns protocol, x_temp1[0..n_by_p*p-1];
      @ ensures get_type(protocol) == protocol_3;*/
    MPI_Allgather(b_local, n_by_p, MPI_FLOAT, x_temp1, n_by_p, MPI_FLOAT, MPI_COMM_WORLD);

    x_new = x_temp1;
    x_old = x_temp1;

    // ADDED: necessary for loop invariant
    tmp = x_temp1;
    /*@ requires get_type(protocol) == protocol_3;
      @ requires getNext(get_type(protocol)) == protocol_4;
      @ assigns protocol, iter, tmp, x_old, x_new, x_local[0..n_by_p-1];
      @ ensures \valid(x_new + (0..n_by_p*p-1));
      @ ensures isSkip(simpl(getFirst(get_type(protocol))));
      @ ensures getNext(get_type(protocol)) == protocol_4;*/
    /*@ loop invariant 0 <= iter <= NUM_ITER;
      @ loop invariant getFirst(get_type(protocol)) ==
      @  getNext(split (getFirst(\at(get_type(protocol),LoopEntry)),iter));
      @ loop invariant getNext(get_type(protocol)) ==
      @  getNext(\at(get_type(protocol),LoopEntry));
      @ loop invariant \valid(x_old + (0..n_by_p*p-1));
      @ loop invariant \valid(x_new + (0..n_by_p*p-1));
      @ loop invariant \valid(tmp + (0..n_by_p*p-1));
      @ loop invariant \valid(x_local + (0..n_by_p-1));
      @ loop assigns protocol, iter,tmp, x_old, x_new, x_local[0..n_by_p-1];
      @ loop variant NUM_ITER - iter;*/
    // CHANGED: starts at 0 instead of 1, end changed respectively
    //          necessary s.t. while can be used in protocol
    for (iter = 0; iter < NUM_ITER; iter++){
      Jacobi_iteration(A_local, x_local, b_local, x_old, n, p);

      //@ ghost unroll();
      //@ ghost assoc();
      MPI_Allgather(x_local, n_by_p, MPI_FLOAT, x_new, n_by_p, MPI_FLOAT, MPI_COMM_WORLD);

      tmp = x_old;
      x_old = x_new;
      x_new = tmp;
    }
    /*@ ghost
      /@ requires isSkip(simpl(getFirst(get_type(protocol))));
       @ requires getNext(get_type(protocol)) == protocol_4;
       @ assigns protocol;
       @ ensures get_type(protocol) == protocol_4;
       @/
      toskip();@*/

    /** ISSUE: cannot prove is_protocol_for_gather **/
    /*@ requires get_type(protocol) == protocol_4;
      @ ensures isSkip(get_type(protocol));
      @ assigns protocol, x_final[0..n_by_p * p - 1];*/
    MPI_Gather(x_new, n_by_p, MPI_FLOAT, x_final, n_by_p, MPI_FLOAT, 0, MPI_COMM_WORLD);

    // REMOVED: no I/O
    // if (rank == 0) {
    //   printVector(x_new, n);
    // }

    MPI_Finalize();
    // uncomment for sanity check
    // // @ assert \false;
}

/**
 * Parallel jacobi iteration program -- annotated version with a deliberate error.
 * Search ERROR below for the error location.
 *  
 * Adapted from:
 *  "Parallel Programming with MPI" by Peter Pacheco, Morgan Kaufmann, 1997.
 *   parallel_jacobi.c example, Chap. 10, p. 220
 *
 * Version: $Id: parallel_jacobi-with-error-annotated.c 4645 2015-06-09 14:57:16Z edrdo $
 * ParTypes - http://gloss.di.fc.ul.pt/ParTypes
 */
#include <stdio.h>
#include <stdlib.h>
#include <mpi.h>
#include <math.h>

// Protocol header
#include "parallel_jacobi.h"

#define MAX_DIM  1000000
#define NUM_ITER 1000000 
#define MATRIX_DECL(var) float var[MAX_DIM * MAX_DIM]

// External functions
void readMatrix(float* matrix, int dim);
void readVector(float* vector, int dim);
void printVector(float* vector, int dim);
void Jacobi_iteration(float* A_local, float* x_local, float* b_local, float* x_old, int n, int p);

int main( int argc, char** argv){
    int        p;
    int        rank;
    int        n;
    int        n_by_p;
    int        iter;
    int        converged;
    MATRIX_DECL(A_initial);
    MATRIX_DECL(A_local);
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
    _(assume n % p == 0 && (n*n) % p == 0)
    _applyInt(n);
    _applyInt(NUM_ITER);
    n_by_p = n / p;
    if (rank == 0) {
      readMatrix(A_initial, n);
      readVector(b_initial, n);
    }  
    
    MPI_Scatter(A_initial, n_by_p * n, MPI_FLOAT, A_local, n_by_p * n , MPI_FLOAT, 0, MPI_COMM_WORLD); 
    MPI_Scatter(b_initial, n_by_p, MPI_FLOAT, x_local, n_by_p, MPI_FLOAT, 0, MPI_COMM_WORLD);
    MPI_Allgather(b_local, n_by_p, MPI_FLOAT, x_temp1, n_by_p, MPI_FLOAT, MPI_COMM_WORLD);
    x_new = x_temp1;
    x_old = x_temp2;
    _(ghost Cons _cfe = cons(_protocol, _rank))    
    _(ghost Protocol _fe = head(_cfe))
    _(assert foreachLower(_fe) == 1)                     
    _(assert foreachUpper(_fe) == NUM_ITER)   
    _(ghost IntAbs _feBody = foreachBody(_fe))   
    for (iter=1; iter <= NUM_ITER; iter++) {
      _(ghost _protocol = _feBody[iter])
      Jacobi_iteration(A_local, x_local, b_local, x_old, n, p);
      // ERROR: MPI_Allgather call missing. Uncomment the following line for the correct program.
      // MPI_Allgather(x_local, n_by_p, MPI_FLOAT, x_new, n_by_p, MPI_FLOAT, MPI_COMM_WORLD);
      tmp = x_old;
      x_old = x_new;
      x_new = tmp;
      _(assert isSkip(_protocol, _rank))
    } 
    _(ghost _protocol = tail(_cfe))
    MPI_Gather(x_new, n_by_p, MPI_FLOAT, x_final, n_by_p, MPI_FLOAT, 0, MPI_COMM_WORLD);
    if (rank == 0) {
      printVector(x_new, n);
    }
    MPI_Finalize();
    // Uncomment for sanity check 
    // _(assert \false)
} 

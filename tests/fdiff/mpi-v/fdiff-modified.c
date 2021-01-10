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
#include <stdio.h>
#define NUM_ITER 1000000
#define MAX_SIZE 1000000

// External functions
/*@ 
  @ ensures \initialized(data + (0 .. n - 1));
  @*/
int read_array(float* data, int n);

/*@ 
  @ ensures \initialized(data + (0 .. n+1));
  @*/
int read_array_(float* data, int n);



int write_array(float* data, int n);
void compute(float* data, int n);

/*@
  @ ensures \result == MAX_SIZE && \result % procs == 0;
  @ */ 
int read_problem_size(int procs); 


/**
 * ASSUMPTIONS:
 * 10 procs 
 * &status -> MPI_STATUS_IGNORE
 * MPI_Send -> MPI_Ssend 
 **/

int main(int argc,char** argv) {
  int procs = 0, rank = 0, n = 0;
  float localErr = 0.0, globalErr = 0.0; 
  float data[MAX_SIZE+2];       
  float local[MAX_SIZE+2]; 
  int left, right;



  MPI_Init(&argc,&argv);
  MPI_Comm_rank(MPI_COMM_WORLD,&rank);
  MPI_Comm_size(MPI_COMM_WORLD,&procs);

  if (rank == 0) {
    n = read_problem_size(procs); 
    read_array(data,n);
  }

  MPI_Bcast(&n,1,MPI_INT,0,MPI_COMM_WORLD);
  // this assertion should hold after bcast
  // //@ assert n == 1000000;
  
  int local_n = 100000; 

  // changed &local[1] -> local, since valid_buf couldn't be assured otherwise
  // changed local_n -> local_n+1 to assure initialization at local[local_n+1]
  MPI_Scatter(data, local_n, MPI_FLOAT, local, local_n, MPI_FLOAT, 0, MPI_COMM_WORLD);
  // this assertion should hold after scatter
  // //@ assert \initialized(local + (0 .. 100000-1));
  
  //***START*** this shouldnt be necessary, since local should be initialized after scatter
  // in order to remain as close as possible to original fdiff 
  // we assure local to be initialized from 0 .. 100000
  // instead of 0 .. 100000-1
  //
  // because recv requires initialization for its buffer we increase 
  // the upper bound by 1 
  read_array_(local, local_n);
  //@ assert \initialized(local + (0 .. 100000+1));
  //***END*** this shouldnt be necessary, since local should be initialized after scatter

  left = rank == 0 ? procs - 1 : rank - 1;
  right = rank == procs - 1 ? 0 : rank + 1;
  

  //@ assert \valid(&local[0]);
  //@ assert \valid(&local[local_n]);
  // changed n/procs -> local_n
  if (rank == 0) {
    // case right: 0 -> 1
    MPI_Ssend(&local[local_n], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD);

    /*@ ghost 
    unroll();
    assoc();    
    toskip(); 
    @*/
    

    // case right: [1 .. procs-2] -> [2 .. procs-1]
    // skip [1 .. procs-2]
    /*@ ghost 
      int i = 1; 
      l1:; 
      /@
       @ loop invariant 1 <= i <= procs-1; 
       @ loop invariant getFirst(get_type(protocol)) ==
       @   getNext(split (getFirst(\at(get_type(protocol),l1)),i));
       @ loop invariant getNext(get_type(protocol)) ==
       @   getNext(\at(get_type(protocol),l1));
       @ loop assigns protocol, i; 
       @ loop variant procs - 1 - i; 
       @/
      while (i < procs-1) {
        unroll(); 
        assoc();
        toskip();  
        i++;
      }
    @*/

    // case right: procs-1 -> 0
    MPI_Recv(&local[0], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  } 
  else if (rank == procs-1) {
    // case right: 0 -> 1
    //@ ghost toskip();

  //   // case right: [1 .. procs-2] -> [2 .. procs-1]
  //   // skip [1 .. procs-3]
  //   /*@ ghost 
  //     int i = 1; 
  //     l2:; 
  //     /@
  //       loop invariant 0 <= i <= procs-2; 
  //       loop invariant getFirst(get_type(protocol)) ==
  //         getNext(split (getFirst(\at(get_type(protocol),l2)),i));
  //       loop invariant getNext(get_type(protocol)) ==
  //         getNext(\at(get_type(protocol),l2));
  //       loop assigns protocol, i; 
  //       loop variant procs - 2 - i; 
  //     @/
  //     while (i < procs-2) {
  //       unroll(); 
  //       assoc();
  //       toskip();  
  //       i++;
  //     }
      
  //     unroll(); 
  //     assoc(); 
  //   @*/
  //   MPI_Recv(&local[0], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  //   // nothing more to skip

    // case right: procs-1 -> 0
    MPI_Ssend(&local[local_n], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
  } else {
    // case right: 0 -> 1
    if (rank == 1) {
      MPI_Recv(&local[0], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    }
    /*@ ghost 
      else {
        toskip();
      }
    @*/
  //   // case right: [1 .. procs-2] -> [2 .. procs-1]
  //   // skip [2 .. rank-1]
  //   /*@ ghost 
  //     if (rank != 1) {
  //       int i = 2; 
  //       l4:; 
  //       /@
  //         loop invariant 0 <= i <= rank; 
  //         loop invariant getFirst(get_type(protocol)) ==
  //           getNext(split (getFirst(\at(get_type(protocol),l4)),i));
  //         loop invariant getNext(get_type(protocol)) ==
  //           getNext(\at(get_type(protocol),l4));
  //         loop assigns protocol, i; 
  //         loop variant rank - i; 
  //       @/
  //       while (i < rank) {
  //         unroll(); 
  //         assoc();
  //         toskip();  
  //         i++;
  //       }
        
  //       unroll(); 
  //       assoc(); 
  //     }
  //   @*/
  //   MPI_Recv(&local[0], 1, MPI_FLOAT, left, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  //   // skip [rank+1 .. procs-2]
  //   /*@ ghost 
  //     int i = rank+1; 
  //     l5:; 
  //     /@
  //       loop invariant rank+1 <= i <= procs-1; 
  //       loop invariant getFirst(get_type(protocol)) ==
  //         getNext(split (getFirst(\at(get_type(protocol),l5)),i));
  //       loop invariant getNext(get_type(protocol)) ==
  //         getNext(\at(get_type(protocol),l5));
  //       loop assigns protocol, i; 
  //       loop variant procs - 1 - i; 
  //     @/
  //     while (i < procs - 1) {
  //       unroll(); 
  //       assoc();
  //       toskip();  
  //       i++;
  //     }
  //   @*/
    
  //   // case right: [1 .. procs-2] -> [2 .. procs-1]
  //   // skip [1 .. rank-1]
  //   /*@ ghost 
  //     int i6 = 1; 
  //     l6:; 
  //     /@
  //       loop invariant 0 <= i6 <= rank; 
  //       loop invariant getFirst(get_type(protocol)) ==
  //         getNext(split (getFirst(\at(get_type(protocol),l6)),i6));
  //       loop invariant getNext(get_type(protocol)) ==
  //         getNext(\at(get_type(protocol),l6));
  //       loop assigns protocol, i6; 
  //       loop variant rank - i6; 
  //     @/
  //     while (i6 < rank) {
  //       unroll(); 
  //       assoc();
  //       toskip();  
  //       i6++;
  //     }
      
  //     unroll(); 
  //     assoc(); 
  //   @*/
  //   MPI_Ssend(&local[local_n], 1, MPI_FLOAT, right, 0, MPI_COMM_WORLD);
  //   // skip [rank+1 .. procs-2]
  //   /*@ ghost 
  //     int i7 = rank+1; 
  //     l7:; 
  //     /@
  //       loop invariant rank+1 <= i7 <= procs - 1; 
  //       loop invariant getFirst(get_type(protocol)) ==
  //         getNext(split (getFirst(\at(get_type(protocol),l7)),i7));
  //       loop invariant getNext(get_type(protocol)) ==
  //         getNext(\at(get_type(protocol),l7));
  //       loop assigns protocol, i7; 
  //       loop variant procs - 1 - i7; 
  //     @/
  //     while (i7 < procs - 1) {
  //       unroll(); 
  //       assoc();
  //       toskip();  
  //       i7++;
  //     }
  //   @*/

    // case right: procs-1 -> 0
    //@ ghost toskip();
  }
  
  //@ assert \initialized(&localErr);
  //@ assert \initialized(&globalErr);
  MPI_Reduce(&localErr,&globalErr,1,MPI_FLOAT,MPI_MAX,0,MPI_COMM_WORLD);

  //changed &local[1] -> local, since initiliazation couldn't be assured otherwise
  MPI_Gather(local,local_n,MPI_FLOAT,data,local_n,MPI_FLOAT,0,MPI_COMM_WORLD);  
  MPI_Finalize();

  //@ assert \false;
}
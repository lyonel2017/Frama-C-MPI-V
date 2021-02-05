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

/*@ requires len > 0;
  @ requires \valid(v + (0..(len-1)));
  @ assigns v[0 .. len-1];
  @*/
void Scan_vector(float* v, int len);

/*@ requires \valid(x + (0..(n-1)));
  @ requires \valid(y + (0..(n-1)));
  @ requires n > 0;
  @ assigns \result;
*/
float Serial_dot(float *x, float *y, int n);

/*@ assigns \nothing;
  @ ensures MAXLEN > \result > 0;
  @*/
int getProblemSize(int procs);

/*@ axiomatic MPI_aux_driver{
  @ logic logic_protocol protocol_1;
  @ logic logic_protocol protocol_2;
  @ logic logic_protocol protocol_3;
  @ logic logic_protocol protocol_4;
  @ logic logic_protocol protocol_foo_0 (integer i);
}*/

/**
 * CHANGES:
 * 1. Send -> Ssend
 * 2. n -> 1000000 (static problem size)
 * 3. status -> MPI_STATUS_IGNORE
 **/
int main(int argc, char** argv)
{
  int    procs = 0, rank = 0, i = 0;
  float  dot = 0, local_dot = 0, remote_dot = 0;
  float  local_x[MAXLEN];
  float  local_y[MAXLEN];
  float  temp[MAXLEN];

  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &procs);

  /*@ requires get_type(protocol) == the_protocol;
    @ requires isSkip(getNext(get_type(protocol)));
    @ assigns remote_dot,i,protocol;
    @ ensures isSkip(get_type(protocol));*/
  if (rank == 0) {
    //@ ghost l0:;
    /*@ requires get_type(protocol) == the_protocol;
      @ requires isSkip(getNext(get_type(protocol)));
      @ assigns remote_dot,i,protocol;
      @ ensures isSkip(get_type(protocol));
      @*/
    /*@ loop invariant 1 <= i <= procs;
      @ loop invariant i < procs ==> getFirst(get_type(protocol)) ==
      @   getNext(split(getFirst(\at(get_type(protocol),l0)),i));
      @ loop invariant i < procs ==> getNext(get_type(protocol)) ==
      @   getNext(\at(get_type(protocol),l0));
      @ loop invariant i == procs ==> isSkip(get_type(protocol));
      @ loop assigns protocol, i, remote_dot;
      @ loop variant procs - i;
      @*/
    for (i = 1; i < procs; i++) {
      //@ ghost unroll();
      //@ ghost assoc();
      /*@ requires getFirst(get_type(protocol)) == protocol_foo_0(i);
        @ assigns remote_dot, protocol;
        @ ensures getFirst(get_type(protocol)) ==
        @   getNext(split(getFirst(\at(get_type(protocol),l0)),i+1));
        @ ensures getNext(get_type(protocol)) ==
        @   getNext(\at(get_type(protocol),l0));
        @*/
      MPI_Recv(&remote_dot, 1, MPI_FLOAT, i, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      /*@ ghost
        if (i == procs-1) {
          /@ requires isSkip(simpl(getFirst(get_type(protocol))));
           @ requires isSkip(getNext(get_type(protocol)));
           @ assigns protocol;
           @ ensures isSkip(get_type(protocol));
           @/
          toskip();
        }
        @*/
    }
  }
  else {
    /*@ ghost
      l3:;
      int j = 1;
      /@ requires get_type(protocol) == the_protocol;
       @ requires isSkip(getNext(get_type(protocol)));
       @ assigns protocol,j;
       @ ensures getFirst(get_type(protocol)) == protocol_foo_0(j);
       @ ensures getFirst(getNext(get_type(protocol))) ==
       @   getNext(split(getFirst(\at(get_type(protocol),l3)),j+1));
       @ ensures getNext(getNext(get_type(protocol))) ==
       @   getNext(\at(get_type(protocol),l3));
       @ ensures isSkip(getNext(getNext(get_type(protocol))));
       @ ensures j == rank;
       @/
      {
        /@ loop invariant 1 <= j <= rank;
        @ loop invariant getFirst(get_type(protocol)) ==
        @  getNext(split(getFirst(\at(get_type(protocol),l3)),j));
        @ loop invariant getNext(get_type(protocol)) ==
        @  getNext(\at(get_type(protocol),l3));
        @ loop assigns protocol, j;
        @ loop variant rank - j;
        @/
        while (j < rank) {
          unroll();
          assoc();
          /@ requires getFirst(get_type(protocol)) == protocol_foo_0(j);
           @ assigns protocol;
           @ ensures getFirst(get_type(protocol)) ==
           @   getNext(split(getFirst(\at(get_type(protocol),l3)),j+1));
           @ ensures getNext(get_type(protocol)) ==
           @   getNext(\at(get_type(protocol),l3));
           @/
          toskip();
          j++;
        }
        /@ requires getFirst(get_type(protocol)) ==
         @   getNext(split(getFirst(\at(get_type(protocol),l3)),j));
         @ requires getNext(get_type(protocol)) ==
         @  getNext(\at(get_type(protocol),l3));
         @ assigns protocol;
         @ ensures getFirst(get_type(protocol)) == protocol_foo_0(j);
         @ ensures getFirst(getNext(get_type(protocol))) ==
         @   getNext(split(getFirst(\at(get_type(protocol),l3)),j+1));
         @ ensures getNext(getNext(get_type(protocol))) ==
         @   getNext(\at(get_type(protocol),l3));
         @/
        {
          unroll();
          assoc();
        }
      }
      @*/
    /*@ requires getFirst(get_type(protocol)) == protocol_foo_0(j);
      @ requires getFirst(getNext(get_type(protocol))) ==
      @   getNext(split(getFirst(\at(get_type(protocol),l3)),j+1));
      @ requires getNext(getNext(get_type(protocol))) ==
      @   getNext(\at(get_type(protocol),l3));
      @ assigns protocol;
      @ ensures getFirst(get_type(protocol)) ==
      @   getNext(split(getFirst(\at(get_type(protocol),l3)),j+1));
      @ ensures getNext(get_type(protocol)) ==
      @   getNext(\at(get_type(protocol),l3));
      @*/
    MPI_Ssend(&local_dot, 1, MPI_FLOAT, 0, 0, MPI_COMM_WORLD);
    /*@ ghost
      j++;
      /@ requires getFirst(get_type(protocol)) ==
       @   getNext(split(getFirst(\at(get_type(protocol),l3)),j));
       @ requires getNext(get_type(protocol)) ==
       @   getNext(\at(get_type(protocol),l3));
       @ assigns protocol, j;
       @ ensures isSkip(get_type(protocol));
       @/
      {
      /@ loop invariant rank + 1 <= j <= procs;
       @ loop invariant getFirst(get_type(protocol)) ==
       @  getNext(split(getFirst(\at(get_type(protocol),l3)),j));
       @ loop invariant getNext(get_type(protocol)) ==
       @  getNext(\at(get_type(protocol),l3));
       @ loop assigns protocol, j;
       @ loop variant procs - j;
       @/
        while (j < procs) {
          unroll();
          assoc();
          /@ requires getFirst(get_type(protocol)) == protocol_foo_0(j);
           @ assigns protocol;
           @ ensures getFirst(get_type(protocol)) ==
           @   getNext(split(getFirst(\at(get_type(protocol),l3)),j+1));
           @ ensures getNext(get_type(protocol)) ==
           @   getNext(\at(get_type(protocol),l3));
           @/
          toskip();
          j++;
        }
        toskip();
      }
      @*/
  }

  MPI_Finalize();
  return 0;
}

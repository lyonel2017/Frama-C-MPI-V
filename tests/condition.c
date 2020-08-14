#include "mpi.h"

/*@ axiomatic test{
  @ predicate test(integer r1, integer r2) = r1 + 5 == r2;
  @ lemma is_no_id: \forall integer a,b; test(a,b) ==> a != b;
  @ lemma is_injective1: \forall integer a1, a2, b;  test(a1, b) && test(a2, b) ==> a1 == a2;
  @ lemma is_injective2: \forall integer a, b1, b2;  test(a, b1) && test(a, b2) ==> b1 == b2;
  @ // WP does not unfolding predicates if the predicate has linked parameters (non free variables)
  @ lemma is_surjective1: \forall integer a; \exists integer b; a + 5 == b;
  @ lemma is_surjective2: \forall integer b; \exists integer a; a + 5 == b;

  @  // Some properties that are not require but are logical deduction
  @ lemma test1 : \forall integer a1, b1, a2, b2; test(a1,b1) && test(a2,b2) ==>
  @                                      (test(a1,b2) ==> a1 == a2 && b1 == b2);
  @ lemma test2 : \forall integer a1, b1, a2, b2; test(a1,b1) && test(a2,b2) ==>
  @                                      (!test(a1,b2) ==> a1 != a2 && b1 != b2);
  @ lemma test3 : \forall integer a1, b1, a2, b2; test(a1,b1) && test(a2,b2) ==>
  @                                      (test(a1,b2) ==> test(a2,b1));
}*/


/*@ axiomatic test2{

  @ predicate c1(integer r) = 0 <= r < 2;
  @ predicate c2(integer r) = 5 <= r < 7;

  @ predicate c3(integer r) = 2 <= r < 5;
  @ predicate c4(integer r) = 7 <= r < 10;

  @ predicate c12(integer r1, integer r2) = c1(r1) && c2(r2);
  @ predicate c34(integer r1, integer r2) = c3(r1) && c4(r2);
  @ predicate default(integer r1, integer r2) = !c12(r1,r2) && !c34(r1,r2);
}*/


// pas d'appelle de procedure dans un premier temps (peut marcher si les communication sont toujour interne a la fonction, send est recve subit la meme suraproximation)
// pas de nouveau communicateur, WP le support pas l'allocation dynamique


// Use the new specification language of RPP to write those properties

/*@ requires 0 <= r1 < 5 && 5 <= r2 < 10;*/
void f(int r1, int r2){
  int d = r1 + 5;
  int s = r2 - 5;

  /*@ assert satisfies_relation_behavior_1:
    @   c12(r1, r2) ==>
    @   test(r1,d) && test(s,r2);*/
  /*@ assert satisfies_relation_behavior_2:
    @   c34(r1, r2) ==>
    @   test(r1,d) && test(s,r2);*/

  /*@ assert not_equal: r1 != r2;*/

  /*@ assert disjointe_behavior:
    @   !(c12(r1, r2) && c34(r1,r2));*/
  /*@ assert complete_behavior:
    @   c12(r1, r2) || c34(r1,r2) || default(r1,r2);*/

  /*@ assert dijonction_1: !c1(r1) && c2(r2) ==> !test(r1,r2);*/
  /*@ assert dijonction_2: c1(r1) && !c2(r2) ==> !test(r1,r2);*/

  /*@ assert dijonction_3: !c3(r1) && c4(r2) ==> !test(r1,r2);*/
  /*@ assert dijonction_4: c3(r1) && !c4(r2) ==> !test(r1,r2);*/

  return;
}

/*@ requires 0 <= rank1 && 0 <= rank2 ;
  @ requires test(rank1,rank2);*/
void color (int rank1, int rank2){
  /*@ ghost int color1 = 0;*/

  if (rank1 < 5) {
    /*@ ghost color1 ++;*/
  } else{
    if (rank1 < 10){
    }
  }

  //----------------------------------
  /*@ ghost int color2 = 0;*/

  if (rank2 < 5) {
  } else{
    if (rank2 < 10){
      /*@ ghost color2 ++;*/
    }
  }

  /*@ assert color1 == color2;*/
}



int main(int argc, char **argv){
  int data = 0;
  int my_rank = 0, num_procs = 0;
  /* Initialize the infrastructure necessary for communication */
  MPI_Init(&argc, &argv);

  /* Identify this process */
  MPI_Comm_rank(MPI_COMM_WORLD, &my_rank);

  /* Find out how many total processes are active */
  MPI_Comm_size(MPI_COMM_WORLD, &num_procs);

  /* Until this point, all programs have been doing exactly the same.
     Here, we check the rank to distinguish the roles of the programs */
  if (my_rank < 5) {

    data = my_rank;
    /* Send messages to other processes with my_rank + 5*/
    MPI_Ssend(&data, 1, MPI_INT, my_rank + 5, 0, MPI_COMM_WORLD);
  } else{
    if (my_rank < 10){

      /* Receive message from process my_rank-5 */
      MPI_Recv(&data, 1, MPI_INT, my_rank-5, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    }
  }

  /* Tear down the communication infrastructure */
  MPI_Finalize();
  return 0;
}

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
  @ predicate c2(integer r) = 5 <= r < 8;

  @ predicate c3(integer r) = 2 <= r < 5;
  @ predicate c4(integer r) = 8 <= r < 10;
}*/



void f(int r1, int r2){
  int d = r1 + 5;
  int s = r2 - 5;

  //relationnelle: use the new notation

  /*@ assert test(s,d) ==> (c2(d) <==> c1(s));*/  //????????????


  /*@ assert c1(s) && c2(d) ==> s != d;*/ // ?????????



  return;
}



int main(int argc, char **argv)
{
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
    /*@ assert satisfies_relation_behavior_1:
      @   c1(__MPI_COMM_WORLD_rank_ACSL) ==>
      @   test(__MPI_COMM_WORLD_rank_ACSL,my_rank + 5);*/
    /*@ assert satisfies_relation_behavior_2:
      @   c3(__MPI_COMM_WORLD_rank_ACSL) ==>
      @   test(__MPI_COMM_WORLD_rank_ACSL,my_rank + 5);*/
    /*@ assert complete_behavior:
      @   c1(__MPI_COMM_WORLD_rank_ACSL) || c3(__MPI_COMM_WORLD_rank_ACSL);*/
    /*@ assert disjointe_behavior:
      @   !(c1(__MPI_COMM_WORLD_rank_ACSL) && c3(__MPI_COMM_WORLD_rank_ACSL));*/
    MPI_Ssend(&data, 1, MPI_INT, my_rank + 5, 0, MPI_COMM_WORLD);
  } else{
    if (my_rank < 10){

      /* Receive message from process my_rank-5 */
      /*@ assert satisfies_relation_behavior_1:
	@   c2(__MPI_COMM_WORLD_rank_ACSL) ==>
	@   test(my_rank-5,__MPI_COMM_WORLD_rank_ACSL);*/
      /*@ assert satisfies_relation_behavior_2:
	@   c4(__MPI_COMM_WORLD_rank_ACSL) ==>
	@   test(my_rank-5,__MPI_COMM_WORLD_rank_ACSL);*/
      /*@ assert complete_behavior:
	@   c2(__MPI_COMM_WORLD_rank_ACSL) || c4(__MPI_COMM_WORLD_rank_ACSL);*/
      /*@ assert disjointe_behavior:
	@   !(c2(__MPI_COMM_WORLD_rank_ACSL) && c4(__MPI_COMM_WORLD_rank_ACSL));*/
      MPI_Recv(&data, 1, MPI_INT, my_rank-5, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    }
  }

  /* Tear down the communication infrastructure */
  MPI_Finalize();
  return 0;
}

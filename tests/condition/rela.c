/*@ axiomatic test{
  @ predicate test(integer r1, integer r2) = r1 + 5 == r2;
  @ predicate c1(integer r) = 0 <= r < 5;
  @ predicate c2(integer r) = 5 <= r < 10;
  @ lemma bounds1: \forall integer a,b; c1(a) && test(a,b) ==> c2(b);
  @ lemma bounds2: \forall integer a,b; c2(b) && test(a,b) ==> c1(a);
  @ lemma is_no_id : \forall integer a,b; test(a,b) ==> a != b;
  @ lemma is_injective1 : \forall integer a1, a2, b;  test(a1, b) && test(a2, b) ==> a1 == a2;
  @ lemma is_injective2: \forall integer a, b1, b2;  test(a, b1) && test(a, b2) ==> b1 == b2;
  @ lemma is_surjective1: \forall integer a;  a >= 0 ==> \exists integer b; test(a, b) && b >= 0;
  @ lemma is_surjective2: \forall integer b; b >= 0 ==> \exists integer a; test(a, b) && a >= 0;
}*/

// WP does not support unfolding of predicates if the predicate has as parameter linked (non free) variables

//check for overflow/domaine of use

void f(int r1, int r2){
  int d = r1 + 5;
  int s = r2 - 5;
  /*@ assert test(r1,r2) ==> s == r1 && d == r2;*/
  /*@ assert !test(r1,r2) ==> s != r1 && d != r2;*/
  return;
}

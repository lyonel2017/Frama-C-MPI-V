int f(int x){
  if(10 <= x && x <= 20){
    /*@ assert 9 <= x <= 17 || 18 <= x <= 21;*/ // complete
    /*@ assert !(9 <= x <= 17 && 18 <= x <= 21);*/ // disjointe
  }
  return x;
}

//#Safe
/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-07-02
 */

int main(){
  int r;
  int x = __VERIFIER_nondet_int();
  if (x < 2) return;
  _Bool overflow = __builtin_sadd_overflow(2147483647, x, &r);
  //@ assert overflow;
}

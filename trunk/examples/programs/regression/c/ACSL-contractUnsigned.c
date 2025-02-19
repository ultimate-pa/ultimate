//#Safe
/* 
 * Test for ACSL contracts using unsigned.
 * 
 * Author: schuessf@informatik.uni-freiburg.de
 * Date: 2024-02-23
 * 
 */

//@ ensures \result < 3;
unsigned f(unsigned x) {
  if (x < 3) return x;
  return 0;
}

int main() {
  unsigned r = f(__VERIFIER_nondet_uint());
  //@ assert r < 3;
}

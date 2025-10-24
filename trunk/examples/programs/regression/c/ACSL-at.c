// #Safe
/*
 * Date: 2025-01-08
 * Author: schuessf@informatik.uni-freiburg.de
 *
 * Demonstrate our support for \at in ACSL.
 */

int g;

//@ requires g > 0;
//@ ensures g < \at(g, Old);
void div() {
  g = g / 2;
  //@ loop invariant g < \at(g, Pre);
  while (__VERIFIER_nondet_int()) {
    g = g / 2;
  }
}

int main() {
  int x = __VERIFIER_nondet_int();
  g = x;
  if (g > 0) {
    div();
    //@ assert g < x;
  }
}

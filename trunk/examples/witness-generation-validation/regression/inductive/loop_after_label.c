// #Safe
/*
 * Date: 2026-10-09
 * Author: schuessf@informatik.uni-freiburg.de
 *
 * Test that the location of a loop after a label is correctly preserved.
 */

int main() {
  int x = 0;
  // Just to make sure that the label is retained
  if (__VERIFIER_nondet_int()) {
	goto label;  
  }
  label:
  while (__VERIFIER_nondet_int()) {
    x++;
  }
  //@ assert x >= 0;
}

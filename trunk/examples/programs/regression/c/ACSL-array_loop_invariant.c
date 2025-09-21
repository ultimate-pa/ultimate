// #Safe
/*
 * Date: 2025-01-07
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

int main() {
  int* a = malloc(sizeof(int));
  a[0] = 7;
  //@ loop invariant a[0] == 7;
  while (__VERIFIER_nondet_int());
  //@ assert *a == 7;
}

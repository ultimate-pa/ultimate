// #Safe
/*
 * Date: 2025-01-13
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

int main() {
  int n = __VERIFIER_nondet_ushort();
  int* a = malloc(n * sizeof(int));
  //@ loop invariant \forall int j; (0 <= j && j < i) ==> a[j] == 42;
  for (int i=0; i<n; i++) {
    a[i] = 42;
  }
}

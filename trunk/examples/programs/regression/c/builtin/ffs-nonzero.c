//#Unsafe

/*
 * Dominik (2024-10-16):
 * Our implementation of ffs() was buggy and blocked for all values other than 0,
 * because it accidentally used an arithmetic right-shift rather than a logical right-shift.
 */

extern int __VERIFIER_nondet_int();

int main() {
  int y = __VERIFIER_nondet_int();
  ffs(y);
  //@ assert y == 0;
}

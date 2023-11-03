//#Nonterminating

/*
 * Extracted from the concurrent benchmark set: svcomp/weaver/bench-exp*.wvr.c
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2022-08-01
 *
 */

extern unsigned int  __VERIFIER_nondet_uint(void);

extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}

unsigned int x, n;

int main() {
  // initialize global variables
  x = __VERIFIER_nondet_uint();
  n = __VERIFIER_nondet_uint();

  // main method
  assume_abort_if_not(x > 0);

  while (x < n) {
    x = x + x;
  }

  return 0;
}

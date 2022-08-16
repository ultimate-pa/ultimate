//#Nonterminating

/*
 * Extracted from the concurrent benchmark: svcomp/weaver/popl20-more-nonblocking-counter-alt2.wvr.c
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

unsigned int M, counter, C;

int main() {
  // initialize global variables
  C = __VERIFIER_nondet_uint();
  M = __VERIFIER_nondet_uint();
  assume_abort_if_not(M > 0);

  unsigned int i = 0;
  while (i < M) {
    __VERIFIER_atomic_begin();
    if (counter > 0) {
      counter = counter - C;
      i++;
    }
    __VERIFIER_atomic_end();
  }

  return 0;
}

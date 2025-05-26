//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2025-05-08
 */

extern long long __VERIFIER_nondet_longlong();

#include <limits.h>

int main() {
	long long x = __VERIFIER_nondet_longlong();
  long long res = x > INT_MIN && x < INT_MAX ? INT_MAX * x : LLONG_MAX;
	return 0;
}

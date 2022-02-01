/*
 * Date: 2012-06-03
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * 2-lex ranking function: f(p, q, *q) = (q, *q)
 *
 */
#include <stdlib.h>

int main() {
	int *p = malloc(10 * sizeof(int));
	int *q = p;
	while (q < p + 10) {
// 		if (__VERIFIER_nondet_int()) {
			q++;
// 		} else {
//			(*q)--;
// 		}
			int a = *q;
	}
	return 0;
}

/*
 * Date: 2012-06-03
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * 2-lex ranking function: f(p, q, *q) = (p + 1048 * sizeof(int) - q, *q)
 *
 */
#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int main() {
	int *p = malloc(1048 * sizeof(int));
	int *q = p;
	while (*q >= 0 && q < p + 1048 * sizeof(int)) {
		if (__VERIFIER_nondet_int()) {
			q++;
		} else {
			(*q)--;
		}
	}
	return 0;
}

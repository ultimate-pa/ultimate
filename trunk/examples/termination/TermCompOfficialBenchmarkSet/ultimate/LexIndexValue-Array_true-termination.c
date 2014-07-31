/*
 * Date: 2012-06-03
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * 2-lex ranking function: f(k, a[k], a[0], a[1048]) = (1048 - k, a[k])
 *
 */
#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int main() {
	int a[1048];
	int k = 0;
	while (a[k] >= 0 && k < 1048) {
		if (__VERIFIER_nondet_int()) {
			k++;
		} else {
			a[k]--;
		}
	}
	return 0;
}

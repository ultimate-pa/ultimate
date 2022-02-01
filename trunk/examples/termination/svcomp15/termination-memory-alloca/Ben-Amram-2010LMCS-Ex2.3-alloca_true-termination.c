#include <stdlib.h>

/*
 * Program from Ex.2.3 of
 * 2010LMCS - Ben-Amram - Size-Change Termination, Monotonicity Constraints and Ranking Functions
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);


int main() {
        int *x = alloca(sizeof(int));
        int *y = alloca(sizeof(int));
        int *z = alloca(sizeof(int));
	*x = __VERIFIER_nondet_int();
	*y = __VERIFIER_nondet_int();
	*z = __VERIFIER_nondet_int();

	while (*x > 0 && *y > 0 && *z > 0) {
		if (*y > *x) {
			*y = *z;
			*x = __VERIFIER_nondet_int();
			*z = *x - 1;
		} else {
			*z = *z - 1;
			*x = __VERIFIER_nondet_int();
			*y = *x - 1;
		}
	}
	return 0;
}

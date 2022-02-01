#include <stdlib.h>

/*
 * Program from Fig.1 of
 * 2005CAV - Bradley,Manna,Sipma - Linear Ranking with Reachability
 * Modified version that can be nonterminating because we allow that inputs of
 * gcd may be zero.
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);


int gcd(int *y1, int *y2) {
	while (*y1 != *y2) {
		if (*y1 > *y2) {
			*y1 = *y1 - *y2;
		} else {
			*y2 = *y2 - *y1;
		}
	}
	return *y1;
}

int main() {
        int *y1 = alloca(sizeof(int));
	int *y2 = alloca(sizeof(int));
	*y1 = __VERIFIER_nondet_int();
	*y2 = __VERIFIER_nondet_int();
	if (*y1 >= 0  && *y2 >= 0) {
		gcd(y1, y2);
	}
	return 0;
}



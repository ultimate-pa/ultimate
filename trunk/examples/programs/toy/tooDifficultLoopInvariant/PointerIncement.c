/*
 * Date: 2014-09-09
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Another simplified version of the LexIndexValue-Pointer example.
 *
 */
#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int main() {
	int *p = malloc(1048 * sizeof(int));
	int *q = p;
	while (q < p + 1048 && *q >= 0) {
		q++;
	}
	return 0;
}

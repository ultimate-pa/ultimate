//#Safe
/*
 * Author: ???
 * Note: The result of this test is not manually verified. DD just added the missing header based on some Ultimate results. 
 * 
 */

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
	int *p = malloc(400 * sizeof(int));
	int *q = p;
	while (q < p + 400 && *q >= 0) {
		q++;
	}
	return 0;
}

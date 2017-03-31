//#Unsafe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 *         greitsch@informatik.uni-freiburg.de
 * Date: 2016-08-09
 * 
 */

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

#include <stdlib.h>

int nonMain(void) {
	float *p = malloc(sizeof(float));
	*p = 1.0;
	*p = *p + 1.0;
	float f = *p;
	if (f == 2.0) {
		__VERIFIER_error();
	}

	free(p);
	return 0;
}

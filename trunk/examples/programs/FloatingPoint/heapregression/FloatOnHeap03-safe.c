//#Safe
//
// Author: greitsch@informatik.uni-freiburg.de
//
// Date:   2017-03-31

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

#include <stdlib.h>

int nonMain()
{
	void *heapspace = malloc(sizeof(long double));

	float *f = heapspace;
	unsigned char *c = heapspace;

	*f = 3.14159265358979323846264338327950288419716939937510;

	if (*c != 219) {
		__VERIFIER_error();
	}


	return 0;
}

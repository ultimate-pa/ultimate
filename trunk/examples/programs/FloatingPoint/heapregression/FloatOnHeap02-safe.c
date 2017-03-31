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
	int *i = heapspace;

	*f = 3.14159265358979323846264338327950288419716939937510;

	if (*i != 1078530011) {
		__VERIFIER_error();
	}


	return 0;
}

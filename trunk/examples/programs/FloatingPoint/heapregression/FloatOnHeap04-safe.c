//#Safe
//
// Author: greitsch@informatik.uni-freiburg.de
//
// Date:   2017-03-31

#include <stdlib.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int nonMain()
{
	void *heapspace = malloc(sizeof(long double));

	float *f = heapspace;
	unsigned char *c = heapspace;

	*f = 3.14159265358979323846264338327950288419716939937510;

	if (c[2] != 73) {
		__VERIFIER_error();
	}

	free(heapspace);

	return 0;
}

//#Safe
//
// Author: greitsch@informatik.uni-freiburg.de
//
// Date:   2017-03-31

#include <stdlib.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int nonMain()
{
	void *heapspace = malloc(sizeof(int));

	float *f = heapspace;
	int *i = heapspace;
	unsigned int *ui = heapspace;
	char *c = heapspace;
	unsigned char *uc = heapspace;

	*i = -1082130432;

	if (*uc != 0) {
		__VERIFIER_error();
	}

	if (*c != 0) {
		__VERIFIER_error();
	}

	if (uc[1] != 0) {
		__VERIFIER_error();
	}

	if (uc[2] != 128) {
		__VERIFIER_error();
	}

	if (uc[3] != 191) {
		__VERIFIER_error();
	}

	if (*f != -1.0f) {
		__VERIFIER_error();
	}

	if (*ui != 3212836864) {
		__VERIFIER_error();
	}

	if (c[2] != -128) {
		__VERIFIER_error();
	}

	if (c[3] != -65) {
		__VERIFIER_error();
	}

	free(heapspace);

	return 0;
}

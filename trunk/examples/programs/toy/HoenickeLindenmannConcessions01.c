// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-11-29
//
// In order to allow a high efficiency our memory model makes concessions to
// soundness.
// We incorrectly claim that the following program is incorrect, although
// this program is correct on x86 Linux systems.

#include <stdio.h>
#include <stdlib.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main() {
	unsigned int *p = malloc(sizeof(int));
	*p = 259U;
	unsigned char *q = (unsigned char *) p;
	unsigned char c;
	c = *q;
	printf("%u\n",c);
	printf("%p\n",q);
	q++;
	c = *q;
	printf("%u\n",c);
	printf("%p\n",q);
	if (c != 1) {
		__VERIFIER_error();
	}
// 	q++;
// 	c = *q;
// 	printf("%u\n",c);
// 	printf("%p\n",q);
// 	q++;
// 	c = *q;
// 	printf("%u\n",c);
// 	printf("%p\n",q);
// 	q++;
// 	q++;
// 	q++;
// 	q++;
	return 0;
}

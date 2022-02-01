//#Unsafe
// Author: lindenmm@informatik.uni-freiburg.de
// Date: 16.08.2012

#include <stdlib.h>

typedef struct
{
	int nr, nr0;
	char c;
	_Bool b;
	int test;
} myStruct;

void test(int* a)
{
	free(a);
}

int main(void)
{
	int *a = (int*) malloc(5 * sizeof(int));
	test(a);
	free(a); // double free on a

	struct f
	{
		int i, j;
		char p;
	} foo;
	a = (int*) malloc(sizeof(struct f));
	free(a);
	a = (int*) malloc(sizeof(myStruct));
	free(a);
	a = (int*) malloc(sizeof(foo));
	free(a);
	int x = sizeof(int);
	a = (int*) malloc(4);
	*a = 4;

	_Bool *b = (_Bool*) malloc(1);
	free(b);

	int *c;
	c = a;
	*a = *c;
	if (*a & *c) {
		*a /= *c;
	} else if (*a >> 3) {
		*a *= *c;
	} else if (3 << *c) {
		*a += *c;
	} else if (*a | *c && *a^*c) {
		// stupid condition ...
		*a -= *c;
		*a %= *c;
	}
	*a <<= 3;
	if((*a)++) {
		// nothing
	} else if((*a)--) {
		// nothing
	} else if (++(*a)) {

	} else if (++*c) {

	}
	a--;
	++c;
	free(a);
	free(c); // double free on c
}

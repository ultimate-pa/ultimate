//#nonterminating
/*
 * Date: 2016-09-07
 * Author: Matthias Heizmann
 * 
 */

#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);


int mountain(int *x)
{
	int *y;

	for (; *y;)
		;
	return 0;
}

int hill(int useless, int *x)
{
	cstrlen(x);
	return 0;
}

int main() {
    int length1 = __VERIFIER_nondet_int();
    int length2 = __VERIFIER_nondet_int();
    if (length1 < 1) {
        length1 = 1;
    }
    if (length2 < 1) {
        length2 = 1;
    }
    int* nondetString1 = (int*) alloca(length1 * sizeof(int));
    int* x = (int*) alloca(length2 * sizeof(int));
    return hill(0,x);
}



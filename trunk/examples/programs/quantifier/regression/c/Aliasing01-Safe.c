//#Safe
/*
 * Date: September 2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>


int nonMain(int *p, int *q) {
	*p = 23;
	*q = 42;
	if (*p == 42) {
		//@ assert p == q;
	} else {
		//@ assert p != q;
	}
}

int main() {
	int *arg1 = malloc(sizeof(int)), 
		*arg2 = malloc(sizeof(int));
	nonMain(arg1, arg2);
	free(arg1);
	free(arg2);
}


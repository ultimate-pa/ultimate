//#Safe
/*
 * Date: September 2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>

int nonMain(int *p, int *q, int *r) {
	*p = 23;
	*q = 42;
	*r = 101;
	if (*p == 42) {
		//@ assert p == q;
	} else {
		if (*p == 101) {
			//@ assert r == p;
		} else {
			//@ assert r != p && p != q;
		}
	}
}

int main() {
	int *arg1 = malloc(sizeof(int)),
		*arg2 = malloc(sizeof(int)),
		*arg3 = malloc(sizeof(int));
	nonMain(arg1, arg2, arg3);
	free(arg1);
	free(arg2);
	free(arg3);
}



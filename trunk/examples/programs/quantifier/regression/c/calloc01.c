//#Safe
/*
 * Check that memory is allocated and initialized with 0.
 * Date: 2016-02-24
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>
#include <stdio.h>

int nonMain() {
	int *p = calloc(3, sizeof(int));
	int trd = *(p+2);
	printf("%d\n",trd);
	//@ assert trd == 0;
	free(p);
	return 0;
}

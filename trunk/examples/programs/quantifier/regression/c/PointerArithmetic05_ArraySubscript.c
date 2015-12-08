//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-11-08
 * 
 */

#include <stdlib.h>
#include <stdio.h>

int nonMain(void) {
	int **pp = malloc(25*sizeof(int*));
	int *p = malloc(7*sizeof(int));
	pp[19] = p;
	p = p + 3;
	*p = 42;
	int a = pp[19][3];
	printf("%d\n",a);
	if (a != 42) {
		//@ assert \false;
	}
	return 0;
}

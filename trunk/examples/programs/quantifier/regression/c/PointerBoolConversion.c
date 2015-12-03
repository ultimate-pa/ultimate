//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-11-22
 * 
 * 6.3.1.2 of C11 says:
 * When any scalar value is converted to _Bool, the result is 0 if the value 
 * compares equal to 0; otherwise, the result is 1.
 */

#include <stdlib.h>
#include <stdio.h>

int nonMain(void) {
	int *p = malloc(7*sizeof(int));
	_Bool b = p;
	if (b == 0) {
		//@ assert \false;
	}
	p = NULL;
	b = p;
	if (b == 1) {
		//@ assert \false;
	}
	return 0;
}

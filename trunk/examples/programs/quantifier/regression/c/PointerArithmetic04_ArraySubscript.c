//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-09-20
 * 
 */

#include <stdlib.h>

int main(void) {
	int *p = malloc(25*sizeof(int));
 	*(p + 7) = 23;
 	int x = p[7];
	if (x != 23) {
		//@ assert \false;
	}
	x = (&p[11])[-4];
	if (x != 23) {
		//@ assert \false;
	}
	free(p);
	return 0;
}

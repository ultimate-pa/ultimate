//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-08-09
 * 
 */

#include <stdlib.h>

int nonMain(void) {
	float *p = malloc(sizeof(float));
	*p = 1.0;
	*p = *p + 1.0;
	float f = *p;
	//@ assert f == 2.0;
	return 0;
}

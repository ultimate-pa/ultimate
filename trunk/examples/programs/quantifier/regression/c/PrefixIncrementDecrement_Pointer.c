//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-09-10
 * 
 */

#include <stdlib.h>

int main(void) {
	int x;
	int a[2] = { 23, 42 };
	int *p = &a[0];
	int *q = ++p;
	x = *q;
	//@ assert x == 42;
	x = *p;
	//@ assert x == 42;

	q = --p;
	x = *q;
	//@ assert x == 23;
	x = *p;
	//@ assert x == 23;
	return 0;
}

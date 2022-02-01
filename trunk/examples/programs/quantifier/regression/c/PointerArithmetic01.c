//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-09-08
 * 
 */

#include <stdlib.h>

int nonmain(void) {
	int a[7] = { 23, 42, 1048, 7 };
	int *p = &a[0];
	int x;
	
	p = p + 2;
	x = *p;
	//@ assert x == 1048;
	
	p = 1 + p;
	x = *p;
	//@ assert x == 7;
	
	int *q = p - 2;
	x = *q;
	//@ assert x == 42;
	
	int d = p - q;
	//@ assert d == 2;
	
	d = q - p;
	//@ assert d == -2;

	return 0;
}

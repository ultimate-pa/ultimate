//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-09-06
 * 
 */

#include <stdlib.h>

int main(void) {
	int a[2] = { 23, 42 };
	int *p = a;
	p++;
	int x = *p;
	//@ assert x == 42;
	return 0;
}

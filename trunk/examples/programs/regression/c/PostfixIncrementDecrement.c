//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-09-10
 * 
 */

#include <stdio.h>

int main(void) {
	int x = 7;
	int y = x++ + 5;
	//@ assert y == 12;
	//@ assert x == 8;
	int z = x-- + 11;
	//@ assert z == 19;
	//@ assert x == 7;
	printf("%d\n", x);
	return 0;
}

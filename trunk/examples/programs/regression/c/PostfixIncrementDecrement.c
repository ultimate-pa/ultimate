//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-09-10
 * 
 */

#include <stdio.h>

int main(void) {
	int x = 7;
	int y = x++;
	//@ assert y == 7;
	//@ assert x == 8;
	int z = x--;
	//@ assert z == 8;
	//@ assert x == 7;
	printf("%d\n", x);
	return 0;
}

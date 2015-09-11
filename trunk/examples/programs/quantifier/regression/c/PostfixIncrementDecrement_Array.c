//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-09-10
 * 
 */

#include <stdio.h>

int main(void) {
	{
		// test with array that is "off-heap"
		int a[1] = { 7 };
		int y = a[0]++ + 5;
		//@ assert y == 12;
		//@ assert a[0] == 8;
		int z = a[0]-- + 11;
		//@ assert z == 19;
		//@ assert a[0] == 7;
		printf("%d\n", a[0]);
	}

	{
		// test with array that is "on-heap"
		int b[1] = { 7 };
		int *p = &b; // obtaining address requires that array is "on-heap"
		int y = b[0]++ + 5;
		//@ assert y == 12;
		if (b[0] != 8) {
			//@ assert \false;
		}
		int z = b[0]-- + 11;
		//@ assert z == 19;
		if (b[0] != 7) {
			//@ assert \false;
		}
		printf("%d\n", b[0]);
	}
	return 0;
}

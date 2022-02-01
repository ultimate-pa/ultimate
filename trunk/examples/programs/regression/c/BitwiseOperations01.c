// #Safe
/*
 * Translate bitwise operations to uninterpreted funtion symbols.
 * 
 * Date: 19.10.2012
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */
#include <stdio.h>


int main(void) {
	int x, y, z;
	y = 1;
	z = 2;
	x = x & y;
	x = x | y;
	x = x ^ y;
	x = x << y;
	x = x >> y;
	x &= y;
	x |= y;
	x ^= y;
	x <<= y;
	x >>= y;
	printf("%d\n",x);
	if (x != 0) {
		//@ assert \false;
	}
}
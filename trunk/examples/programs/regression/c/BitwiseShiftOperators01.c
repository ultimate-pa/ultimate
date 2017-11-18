//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-11-18
 * 
 */
#include <stdio.h>

int main(void) {
	int a = 5;
	int b = a << 4;
	printf("%d\n",b);
	if (b != 80) {
		//@ assert \false;
	}
	
	// 2^31+1
	unsigned int c = 2147483649;
	unsigned int d = c << 1;
	printf("%u\n",d);
	if (d != 2) {
		//@ assert \false;
	}
	
	int e = 5;
	int f = e >> 1;
	printf("%d\n",f);
	if (f != 2) {
		//@ assert \false;
	}
	
	return 0;
}

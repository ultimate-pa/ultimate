//#Safe
/*
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-09-06
 * 
 */

#include <stdio.h>

int main(void) {
	printf("sizeof(_Bool)=%lu\n", sizeof(_Bool));
	printf("sizeof(char)=%lu\n", sizeof(char));
	printf("sizeof(short)=%lu\n", sizeof(short));
	printf("sizeof(int)=%lu\n", sizeof(int));
	printf("sizeof(long)=%lu\n", sizeof(long));
	printf("sizeof(long long)=%lu\n", sizeof(long long));
	printf("sizeof(float)=%lu\n", sizeof(float));
	printf("sizeof(double)=%lu\n", sizeof(double));
	printf("sizeof(long double)=%lu\n", sizeof(long double));
	printf("sizeof(int*)=%lu\n", sizeof(int*));
	return 0;
}

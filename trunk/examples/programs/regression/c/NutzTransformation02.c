//#Safe
// Test for Alex's treatment of unsigned ints which does the modulo computation
// not after each operation but 
//  - before comparisons (this includes relational operators, equality 
//        operators and checks if a value is (un)equal to zero)
//  - before conversions to signed data types, 
//  - before casts to unsigned data types if the resulting data type has a 
//        larger size, and
//  - before division and modulo operations.
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-09-01

#include <stdio.h>

int main() {
	if (sizeof(int) == 4) {
		unsigned int a = -1;
		// a is 4294967295 but -1 in our representation
		printf("%u\n",a);
		unsigned int b = a / 1024;
		// b is 4194303, but 0 in our representation if we (by mistake) omit
		// the modulo UINT_MAX+1 before the division operation.
		printf("%u\n",b);
		if (b != 4194303) {
			//@ assert \false;
		}
		
		unsigned int c = -32;
		// c is 4294967264, but -32 in our representation
		printf("%u\n",c);
		unsigned int d = c % 13;
		// d is 3, but -6 in our representation if we (by mistake) omit
		// the modulo UINT_MAX+1 before the modulo operation.
		printf("%u\n",d);
		if (d != 3) {
			//@ assert \false;
		}
	}
	return 0;
}

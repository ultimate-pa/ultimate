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
// Date: 2015-09-17

#include <stdio.h>

int main() {
	if (sizeof(short) == 2) {
		unsigned short a = -1;
		// a is 65535 but -1 in our representation
		printf("%u\n",a);
		unsigned long long b = a;
		// b is 65535, but -1 in our representation if we (by mistake) omit
		// the modulo USHORT_MAX+1 before the division operation.
		// using modulo ULONGLONG_MAX+1 does not help.
		if (b != 65535) {
			//@ assert \false;
		}
	}
	return 0;
}

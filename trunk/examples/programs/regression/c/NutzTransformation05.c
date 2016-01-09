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
// Date: 2016-01-05

#include <stdio.h>

int main() {
	if (sizeof(char) < sizeof(int)) {
		unsigned char a = (unsigned char) -1;
		// a is 255 but -1 in our representation
		printf("%u\n",a);
		int b = 500;
		// Before the summation both operands are promoted to signed int because
		// integer promontion is part of unsual arithmetic conversions.
		// The result of the summation has type 'signed int'.
		// Using the Nutz transformation we have to apply the wraparound to the
		// operands of the summation.
		// 
		if (a + a < b) {
			//@ assert \false;
		}
		printf("%d\n",a + a);
	}
	return 0;
}

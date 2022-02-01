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
// Date: 2015-11-22

#include <stdio.h>

int main() {
	if (sizeof(short) == 2) {
		unsigned short a = (unsigned short) -65536;
		// a is 0 but -65536 in our representation
		printf("%u\n",a);
		int b = !a;
		//@ assert b == 1;
		int c = a && 1;
		//@ assert c == 0;
		int d = a || 0;
		//@ assert d == 0;
		int e = (a ? 5 : 17);
		//@ assert e == 17;
		if (a) {
			//@ assert \false;
		}
		while(a) {
			//@ assert \false;
			break;
		}
// 		for (;;a) {
// 			//@ assert \false;
// 			break;
// 		}
		int i=0;
		do {
			i++;
		} while (a);
		//@ assert i == 1;
	}
	return 0;
}

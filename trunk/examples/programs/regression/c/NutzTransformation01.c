//#Safe
// Test for Alex's treatment of unsigned ints which does the modulo computation
// not after each operation but 
//  - before comparisons (this includes relational operators, equality 
//        operators and checks if a value is (un)equal to zero)
//  - before conversions to signed data types, 
//  - before casts to unsigned data types if the resulting data type has a 
//        larger size,
//  - before division and modulo operations,
//  - before array declarations, and
//  - before calls to C library functions.
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-08-31

#include <stdio.h>

int main() {
	if (sizeof(long long) > 4 && sizeof(int) == 4) {
		unsigned int x = 2147483648U;
		printf("%u\n",x);
		x += 2147483648U;
		printf("%u\n",x);
		// now, due to the wraparound the value of x is 0, however we
		// store 2^32 and take this value modulo 2^32 in comparisons
		// if the operands of the comparison are unsigned ints.
		if (x != 0) {
			//@ assert \false;
		}
		signed long long y = x;
		printf("%lld\n",y);
		// now the type of the expression is not unsigned any more
		// it was important that we did the modulo 2^32 at the
		// cast from unsigned to signed
		if (y != 0) {
			//@ assert \false;
		}
	}
	return 0;
}

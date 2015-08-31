//#Safe
// Test for Alex's treatment of unsigned ints which does the modulo computation
// not after operations but before comparisons.
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-08-31

int main() {
	if (sizeof(long long) > 4 && sizeof(int) == 4) {
		unsigned int x = 2147483648U;
		x += 2147483648U;
		// now, due to the wraparound the value of x is 0, however we
		// store 2^32 and take this value modulo 2^32 in comparisons
		// if the operands of the comparison are unsigned ints.
		if (x != 0) {
			//@ assert \false;
		}
		signed long long y = x;
		// now the type of the expression is not unsigned any more
		// it was important that we did the modulo 2^32 at the
		// cast from unsigned to signed
		if (y != 0) {
			//@ assert \false;
		}
	}
	return 0;
}

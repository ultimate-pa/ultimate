//#Safe
// Test that for a zero check values are not converted to int.
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-11-22

#include <stdio.h>

int main() {
	long long x = 4294967296LL;
	
	// converted to int this is sometimes zero
	int y = x;
	printf("%d\n",y);

	// however, if compared to zero is has a different value
	if (x) {
		printf("x is not zero");
	} else {
		//@ assert \false;
	}
	return 0;
}

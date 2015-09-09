// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-09-01
//
// We assume sizeof(int)=4 and sizeof(long)>4.

#include <stdio.h>

int main() {
	// The operand 1L has type long. Due to the usual arithmetic conversions, 
	// 2147483647 is converted to long before the addition, hence there is 
	// not overflow.
	int x = (2147483647 + 1L) - 23;
	printf("%d\n", x);
	return 0;
}

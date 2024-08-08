// #Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2022-11-20
//
// We assume sizeof(int)=4.

#include <limits.h>
#include <stdio.h>


int main() {
	int x = 2147483647;
	int y = 2147483647;
	// Although the value is assigned to a long long
	// the result of the multiplication has type int
	long long z = x * y;
	printf("%lld\n", z);
	return 0;
}

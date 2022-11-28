// #Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2022-11-20
//
// We assume sizeof(int)=4.

#include <limits.h>
#include <stdio.h>


int main() {
	long long x = 2147483647;
	long long y = 2147483647;
	long long z = x * y;
	printf("%lld\n", z);
	return 0;
}

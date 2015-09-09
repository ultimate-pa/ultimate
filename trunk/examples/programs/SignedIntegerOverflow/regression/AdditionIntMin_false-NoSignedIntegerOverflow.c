// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-09-01

#include <stdio.h>

int main() {
	int x = (-2147483648 - 1) + 23;
	printf("%u\n", x);
	return 0;
}

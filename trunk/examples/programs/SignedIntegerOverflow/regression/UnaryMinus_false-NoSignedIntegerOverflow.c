// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-09-09

#include <stdio.h>

int main() {
	int x = -2147483648;
	int y = -x - 23;
	printf("%u\n", y);
	return 0;
}

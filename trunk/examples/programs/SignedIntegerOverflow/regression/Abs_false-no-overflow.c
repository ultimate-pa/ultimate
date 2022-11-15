// Author: heizmann@informatik.uni-freiburg.de
// Date: 2022-11-16
//
// We assume sizeof(int)=4.

#include <stdio.h>
#include <stdlib.h>

int main() {
	int minInt = -2147483647 - 1;
	int x = abs(minInt);
	printf("%d\n", x);
	return 0;
}

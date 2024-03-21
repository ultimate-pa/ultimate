// Author: heizmann@informatik.uni-freiburg.de
// Date: 2022-11-16
//
// We assume sizeof(int)=4.

#include <stdio.h>
#include <stdlib.h>

int main() {
	int smallNumber = -2147483647;
	int x = abs(smallNumber);
	printf("%d\n", x);
	return 0;
}

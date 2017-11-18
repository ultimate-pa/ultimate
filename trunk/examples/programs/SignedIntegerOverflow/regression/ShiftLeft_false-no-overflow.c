// Author: heizmann@informatik.uni-freiburg.de
// Date: 2017-11-18
//
// We assume sizeof(int)=4.

#include <stdio.h>

int main() {
	int maxInt = 2147483647;
	int y = maxInt << 4;
	printf("%d\n", y);
	return 0;
}

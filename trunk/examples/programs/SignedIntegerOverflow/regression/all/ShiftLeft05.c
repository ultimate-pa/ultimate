// #Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2022-11-20
//
// C11 says in Section 6.5.7 on bitwise shift operators:
// Behavior undefined if value of left(!) operand is negative.
//
// We assume sizeof(int)=4 and sizeof(short)=2

#include <stdio.h>

int main() {
	int x = -1;
	int y = 0;
	int z = x << y;
	printf("%d\n", z);
	return 0;
}

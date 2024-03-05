// #Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2022-11-20
//
// C11 says in Section 6.5.7 on bitwise shift operators:
// Behavior undefined if value of right operand is >= width
// of the promoted left operand.
//
// We assume sizeof(int)=4.

#include <stdio.h>

int main() {
	int x = 0;
	int y = 32;
	int z = x << y;
	printf("%d\n", z);
	return 0;
}

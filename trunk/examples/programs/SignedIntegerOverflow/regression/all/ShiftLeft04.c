// #Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2022-11-20
//
// C11 says in Section 6.5.7 on bitwise shift operators:
// Behavior undefined if value of right operand is >= width
// of the promoted left operand.
//
// Here: No problem because the LHS is promoted to int.
//
// We assume sizeof(int)=4 and sizeof(short)=2

#include <stdio.h>

int main() {
	short x = 0;
	short y = 31;
	short z = x << y;
	printf("%d\n", z);
	return 0;
}

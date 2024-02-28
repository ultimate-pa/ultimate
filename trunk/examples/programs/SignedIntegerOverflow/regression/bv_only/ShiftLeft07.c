// #Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2022-11-20
//
// C11 says in Section 6.5.7 on bitwise shift operators:
// Result has to be representable in the type of the LHS
//
//
// We assume sizeof(int)=4

#include <stdio.h>

int main() {
	int x = 4;
	int y = 28;
	int z = x << y;
	printf("%d\n", z);
	return 0;
}

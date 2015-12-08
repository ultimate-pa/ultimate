//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-11-22
//
// 6.3.1.2 of C11 says:
// When any scalar value is converted to _Bool, the result is 0 if the value 
// compares equal to 0; otherwise, the result is 1.
//
// This means expecially that fancy modulo operations lead to unsound results
// in this case.


#include <stdio.h>

int main(void) {
	_Bool b = 2;
	printf("%d\n",b);
	if (b == 0) {
		//@ assert \false;
	}
	unsigned long long ull = 4294967296LL;
	b = ull;
	printf("%d\n",b);
	if (b == 0) {
		//@ assert \false;
	}
	unsigned long long sll = 4294967296LL;
	b = sll;
	printf("%d\n",b);
	if (b == 0) {
		//@ assert \false;
	}
}
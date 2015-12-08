//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-11-22
//
// In 9fbe7b2401b77b66ee97f8fd5151f556b883d59a Ultimate incorrectly says
// that the assert statement can be violated.
//
// Presumed problem: In contradicion to the C standard, the controlling
// expression is converted to int.

#include <stdio.h>

int main(void) {
	unsigned long long x = 4294967296LL;
	switch(x) {
		case 0: {
			printf("I took case 0\n");
			//@ assert \false;
			break;
		}
		default: {
			printf("I took the default case\n");
		}
	}
}
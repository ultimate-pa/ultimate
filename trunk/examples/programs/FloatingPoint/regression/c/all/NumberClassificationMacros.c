//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-07-11
 * 
 * Assert that number classification macros have the same numbers as on
 * my computer. The C standard allows arbitrary distinct values.
 */


#include <stdio.h>
#include <float.h>
#include <math.h>

int main() {
// 	printf("%d", FP_NAN); 
	if (FP_NAN != 0) {
		//@ assert \false;
	}
// 	printf("%d", FP_INFINITE);
		if (FP_INFINITE != 1) {
		//@ assert \false;
	}
// 	printf("%d", FP_ZERO);
		if (FP_ZERO != 2) {
		//@ assert \false;
	}
// 	printf("%d", FP_SUBNORMAL);
		if (FP_SUBNORMAL != 3) {
		//@ assert \false;
	}
// 	printf("%d", FP_NORMAL); 
		if (FP_NORMAL != 4) {
		//@ assert \false;
	}

}

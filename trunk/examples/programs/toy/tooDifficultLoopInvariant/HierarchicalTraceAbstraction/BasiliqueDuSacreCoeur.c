//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-03-04
 *
 *
 */
#include <math.h>

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);


int main() {
    float x, y;

    x = __VERIFIER_nondet_float();
    y = __VERIFIER_nondet_float();
	if (x >= 0 && !(y <= 0)) {
		while (__VERIFIER_nondet_int()) {
// 			if (fpclassify (x) == FP_NORMAL) {
				x = x + y;
// 			} else {
// 				x = x + y;
// 			}
		}
		if (y == 2 && !(x >= 0)) {
			//@ assert \false;
		}
	}
    return 0;
}

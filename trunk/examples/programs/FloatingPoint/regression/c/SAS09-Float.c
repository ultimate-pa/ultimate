//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-07-30
 *
 * Modification of our SAS09 example with floats where we use ">=" instead of
 * "==" in the assert statement.
 * Shows that our Trace Interpolation also works with floats.
 * 
 * Demonstrate two features of the C language (resp. floats).
 * - there is no wraparound (like addition of unsigned ints)
 * - while incrementing we never reach INFINITY
 *
 */
#include <math.h>

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);


int main() {
    float x, y;

    x = 0;
    y = 0;

    while (__VERIFIER_nondet_int()) {
        x = x + 1;
    }
    
    if (x == INFINITY || !(x >= 0)) {
		//@ assert \false;
	}

	//@ assert y >= 0;

    return 0;
}

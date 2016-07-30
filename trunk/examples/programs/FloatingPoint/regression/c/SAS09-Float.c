//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
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


extern double __VERIFIER_nondet_float();
extern double __VERIFIER_nondet_int();


int main() {
    float x, y;

    x = 0;
    y = 0;

    while (__VERIFIER_nondet_int()) {
        x = x + 1;
    }
    
    if (x == INFINITY) {
		//@ assert \false;
	}

	//@ assert x >= 0;
	//@ assert y >= 0;

    return 0;
}

//#Unsafe
/* 
 * Assert statement can be violated if x is a NaN value.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-07-26
 */


float __VERIFIER_nondet_float();

int main() {
	float x = __VERIFIER_nondet_float();
	float y = __VERIFIER_nondet_float();
	if (x == x && y != y) {
		// do nothing
	} else {
		//@ assert \false;
	}

}

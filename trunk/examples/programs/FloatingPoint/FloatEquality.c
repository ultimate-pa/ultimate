//#Unsafe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-07-26
 * 
 */


float __VERIFIER_nondet_float();

int main() {
	float f = __VERIFIER_nondet_float();

	if (f == f) {
		//@ assert \false;
	} else {
		//@ assert \false;
	}

}

//#Unsafe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-07-28
 */


float __VERIFIER_nondet_float();

int main() {
	float x = 1.0;
	if (x == 2.0) {
		// do nothing
	} else {
		//@ assert \false;
	}

}

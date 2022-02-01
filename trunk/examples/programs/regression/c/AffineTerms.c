//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-02-08
 * 
 */

extern int __VERIFIER_nondet_int();

int main() {
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	int z = __VERIFIER_nondet_int();
	
	if (x + y + z > 0) {
		while(__VERIFIER_nondet_int()) {
		// do nothing, break large block encoding
		}
		if (x + y + z <= 0) {
			//@ assert \false;
		}
	}
	return 0;
}
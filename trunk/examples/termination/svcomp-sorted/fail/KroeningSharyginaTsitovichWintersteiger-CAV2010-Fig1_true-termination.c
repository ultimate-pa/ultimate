/*
 * Program from Fig.1 of
 * 2010CAV - Kroening,Sharygina,Tsitovich,Wintersteiger - Termination Analysis with Compositional Transition Invariants
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);


int main() {
	int x = __VERIFIER_nondet_int();
	int debug = 0;

	while (x < 255) {
		if (x % 2 != 0) {
			x--;
		} else {
			x += 2;
		}
		if (debug != 0) {
			x = 0;
		}
	}
	return 0;
}



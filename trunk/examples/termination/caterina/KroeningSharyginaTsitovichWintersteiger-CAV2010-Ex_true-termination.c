/*
 * Program from the example (without number) of
 * 2010CAV - Kroening,Sharygina,Tsitovich,Wintersteiger - Termination Analysis with Compositional Transition Invariants
 *
 * Date: 2014
 * Author: Caterina Urban
 *
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int i = __VERIFIER_nondet_int();
	while (i < 255) {
		if (__VERIFIER_nondet_int()) {
			i = i + 1;
		} else {
			i = i + 2;
		}
	}
	return 0;
}
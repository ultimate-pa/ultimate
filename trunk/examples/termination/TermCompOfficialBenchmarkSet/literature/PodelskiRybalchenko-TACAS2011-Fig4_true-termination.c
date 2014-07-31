/*
 * Program from Fig.4 of
 * 2011TACAS - Podelski,Rybalchenko - Transition Invariants and Transition Predicate Abstraction for Program Termination
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	while (x > 0 && y > 0) {
		if (__VERIFIER_nondet_int()) {
			x = x - 1;
			y = __VERIFIER_nondet_int();
		} else {
			y = y - 1;
		}
	}
	return 0;
}
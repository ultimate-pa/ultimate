/*
 * Program from Fig.1 of
 * 2004LICS - Podelski, Rybalchenko - Transition Invariants
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	while (x >= 0) {
		y = 1;
		while (y < x) {
			y = 2*y;
		}
		x = x - 1;
	}
	return 0;
}
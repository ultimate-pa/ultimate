/*
 * Program from Fig.2 of
 * 2004LICS - Podelski, Rybalchenko - Transition Invariants
 *
 * Date: 2014
 * Author: Caterina Urban, Matthias Heizmann
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	while (x > 0 && y > 0) {
		int old_x = x;
		int old_y = y;
		if (__VERIFIER_nondet_int()) {
			x = old_x - 1;
			y = old_x;
		} else {
			x = old_y - 2;
			y = old_x + 1;
		}
	}
	return 0;
}
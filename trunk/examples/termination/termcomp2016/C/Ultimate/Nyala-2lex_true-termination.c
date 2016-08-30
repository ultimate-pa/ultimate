/*
 * Date: 2013-07-13
 * Author: leike@informatik.uni-freiburg.de
 *
 * Simple test case for the lexicographic template.
 * Has the lexicographic ranking function
 * f(x, y) = <x, y>
 *
 */


extern int __VERIFIER_nondet_int(void);

int main() {
	int x, y;
	while (x >= 0) {
		y = y - 1;
		if (y < 0) {
			x = x - 1;
			y = __VERIFIER_nondet_int();
		}
		if (y < 0) {
			break;
		}
	}
}

/*
 * Date: 2011-12-11
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(x, y) = x
 * provided with the supporting invariant y >= 1.
 */

extern int __VERIFIER_nondet_int(void);

int main()
{
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	if (y < 1) {
		return 0;
	}
	while (x >= 0) {
		x = x - y;
	}
	return 0;
}


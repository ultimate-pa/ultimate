/*
 * Date: 2012-02-12
 * Author: leike@informatik.uni-freiburg.de
 *
 * Ranking function: f(x, y, a, b) = x + y;
 * needs the loop invariant a = b.
 * (More diffcult version of Stockholm.)
 */

extern int __VERIFIER_nondet_int(void);

int main()
{
	int a = __VERIFIER_nondet_int();
	int b = __VERIFIER_nondet_int();
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	if (a != b) {
		return 0;
	}
	while (x >= 0 || y >= 0) {
		x = x + a - b - 1;
		y = y + b - a - 1;
	}
	return 0;
}

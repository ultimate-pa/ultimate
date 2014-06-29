/*
 * Date: 2012-02-12
 * Author: leike@informatik.uni-freiburg.de
 *
 * Ranking function: f(x, a, b) = x;
 * needs the loop invariant b >= a.
 */

extern int __VERIFIER_nondet_int(void);

int main()
{
	int x = __VERIFIER_nondet_int();
	int a = __VERIFIER_nondet_int();
	int b = __VERIFIER_nondet_int();
	if (a != b) {
		return 0;
	}
	while (x >= 0) {
		x = x + a - b - 1;
	}
	return 0;
}

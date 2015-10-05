/*
 * Date: 2013-12-20
 * Author: leike@informatik.uni-freiburg.de
 *
 * An example tailored to the parallel ranking template.
 *
 * A ranking function is
 *
 * f(x, y) = max{x, 0} + max{y, 0}.
 *
 */

extern int __VERIFIER_nondet_int(void);

int main()
{
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	while (1) {
		if (x >= 0) {
			x = x - 1;
		} else {
			if (y < 0) {
				break;
			}
			y = y - 1;
		}
	}
	return 0;
}

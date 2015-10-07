/*
 * Date: 2012-02-12
 * Author: leike@informatik.uni-freiburg.de
 *
 * Does not terminate for 0 <= x <= 10
 * due to rounding in integer division.
 */

extern int __VERIFIER_nondet_int();

int main()
{
	int y = __VERIFIER_nondet_int();
	while (y >= 0 && y <= 10) {
		y = (2*y + 1) / 2;
	}
	return 0;
}

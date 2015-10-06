/*
 * Date: 2012-08-10
 * Author: leike@informatik.uni-freiburg.de
 *
 * This program has the following 2-nested ranking function:
 * f_0(x, y) = y + 1
 * f_1(x, y) = x
 */

extern int __VERIFIER_nondet_int();

int main()
{
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	while (x >= 0) {
		x = x + y;
		y = y - 1;
	}
	return 0;
}

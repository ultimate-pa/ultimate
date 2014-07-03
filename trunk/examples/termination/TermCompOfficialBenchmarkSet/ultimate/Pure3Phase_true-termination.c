/*
 * Date: 2014-06-29
 * Author: leike@informatik.uni-freiburg.de
 *
 * This program has the following 3-phase ranking function:
 * f_0(x, y, z) = z
 * f_1(x, y, z) = y
 * f_2(x, y, z) = x
 *
 * The program does not have a nested ranking function.
 */

extern int __VERIFIER_nondet_int();

int main()
{
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	int z = __VERIFIER_nondet_int();
	while (x >= 0) {
		if (__VERIFIER_nondet_int()) {
			x = x + y;
		} else {
			x = x + z;
		}
		y = y + z;
		z = z - 1;
	}
	return 0;
}

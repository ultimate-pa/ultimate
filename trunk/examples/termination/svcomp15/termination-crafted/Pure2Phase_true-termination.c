/*
 * Date: 2014-03-24
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Simple program that has a 2-phase ranking function but no
 * 2-nested ranking function.
 *
 */

extern int __VERIFIER_nondet_int();

int main()
{
	int y = __VERIFIER_nondet_int();
	int z = __VERIFIER_nondet_int();
	while (z >= 0) {
		y = y - 1;
		if (y >= 0) {
			z = __VERIFIER_nondet_int();
		} else {
			z = z - 1;
		}
	}
	return 0;
}

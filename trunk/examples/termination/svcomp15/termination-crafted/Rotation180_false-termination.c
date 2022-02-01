/*
 * Date: 2013-12-16
 * Author: leike@informatik.uni-freiburg.de
 *
 * Rotates x and y by 90 degrees
 * Does not terminate.
 */

extern int __VERIFIER_nondet_int();

int main ()
{
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	while (1) {
		int old_x = x;
		x = -y;
		y = old_x;
	}
	return 0;
}

/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 *
 * Does not terminate for y >= 5.
 */

extern int __VERIFIER_nondet_int();

int main()
{
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	if (y < 5) {
		return 0;
	}
	while (x >= 0) {
		y -= 1;
	}
	return 0;
}


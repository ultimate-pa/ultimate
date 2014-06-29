/*
 * Date: 2013-12-16
 * Author: leike@informatik.uni-freiburg.de
 *
 * Does not terminate for c >= 0.
 */

extern int __VERIFIER_nondet_int();

int main()
{
	int c = __VERIFIER_nondet_int();
	int x = __VERIFIER_nondet_int();
	while (x >= 0) {
		x += c;
	}
}


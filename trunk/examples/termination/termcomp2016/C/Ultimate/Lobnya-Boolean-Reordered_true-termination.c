/*
 * Date: 2013-07-10
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(x) = x
 *
 */

extern int __VERIFIER_nondet_int();

int main ()
{
	int x = __VERIFIER_nondet_int();
	int b = __VERIFIER_nondet_int();
	while (1) {
		if (!b) {
			break;
		}
		b = __VERIFIER_nondet_int();
		x = x - 1;
		b = (x >= 0);
	}
	return 0;
}

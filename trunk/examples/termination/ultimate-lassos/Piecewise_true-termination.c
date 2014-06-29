/*
 * Date: 08.10.2013
 * Author: leike@informatik.uni-freiburg.de
 *
 * An example tailored to the piecewise ranking template.
 *
 * A ranking function is
 *
 * f(p, q) = min(p, q).
 *
 */

extern int __VERIFIER_nondet_int(void);

int main()
{
	int q = __VERIFIER_nondet_int();
	int p = __VERIFIER_nondet_int();
	while (q > 0 && p > 0) {
		if (q < p) {
			q = q - 1;
			p = __VERIFIER_nondet_int();
		} else if (p < q) {
			p = p - 1;
			q = __VERIFIER_nondet_int();
		} else {
			break;
		}
	}
	return 0;
}

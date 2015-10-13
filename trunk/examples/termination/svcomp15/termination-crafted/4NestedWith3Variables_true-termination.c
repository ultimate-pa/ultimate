/*
 * Date: 2014-06-08
 * Author: leike@informatik.uni-freiburg.de
 *
 * (a, b) is a vector that is rotated around (0, 0) and scaled by a factor of 5.
 * I.e., (a, b) is on an outward spiral around (0, 0).
 *
 * This program terminates because on average, (a, b) is (0, 0),
 * hence q decreases by 1 on average.
 */

extern int __VERIFIER_nondet_int(void);

int main()
{
	int q = __VERIFIER_nondet_int();
	int a = __VERIFIER_nondet_int();
	int b = __VERIFIER_nondet_int();
	while (q > 0) {
		q = q + a - 1;
		int old_a = a;
		a = 3*old_a - 4*b;
		b = 4*old_a + 3*b;
	}
	return 0;
}

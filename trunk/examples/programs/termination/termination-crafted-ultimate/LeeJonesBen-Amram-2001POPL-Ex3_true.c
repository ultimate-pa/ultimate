/*
 * Program from Ex.3 of
 * 2001POPL - Lee,Jones,Ben-Amram - The size-change principle for program termination
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);

int a(int m, int n) {
	if (m <= 0) {
		return n + 1;
	} else {
		if (n <= 0) {
			return a(m - 1, 1);
		} else {
			return a(m - 1, a(m, n - 1));
		}
	}
}

int main() {
	int m = __VERIFIER_nondet_int();
	int n = __VERIFIER_nondet_int();
	if ( m >= 0 && n >= 0) {
		a(m,n);
	}
	return 0;
}

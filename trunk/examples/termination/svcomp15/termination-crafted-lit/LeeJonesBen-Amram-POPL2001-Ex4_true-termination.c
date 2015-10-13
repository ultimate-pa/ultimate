/*
 * Program from Ex.4 of
 * 2001POPL - Lee,Jones,Ben-Amram - The size-change principle for program termination
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);

int p(int m, int n, int r) {
	if (r > 0) {
		return p(m, r-1, n);
	} else {
		if (n > 0) {
			return p(r, n-1, m);
		} else {
			return m;
		}
	}
}

int main() {
	int m = __VERIFIER_nondet_int();
	int n = __VERIFIER_nondet_int();
	int r = __VERIFIER_nondet_int();
	if ( m >= 0 && n >= 0 && r >= 0) {
		p(m,n,r);
	}
	return 0;
}

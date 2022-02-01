/*
 * Program from Fig.1 of
 * 2005ICALP - Bradley,Manna,Sipma - The Polyranking Principle
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);


int main() {
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	int N = __VERIFIER_nondet_int();
	// continue only for values where there won't be any overflow or underflow
	// on systems where sizeof(int)=4 holds.
	if (N >= 536870912 || x >= 536870912 || y >= 536870912 || x < -1073741824) {
		return 0;
	}
	if (x + y >= 0) {
		while (x <= N) {
			if (__VERIFIER_nondet_int()) {
				x = 2*x + y;
				y = y + 1;
			} else {
				x = x + 1;
			}
		}
	}
	return 0;
}



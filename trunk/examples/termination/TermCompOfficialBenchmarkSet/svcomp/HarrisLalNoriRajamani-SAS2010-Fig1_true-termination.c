/*
 * Program from Fig.1 of
 * 2010SAS - Harris, Lal, Nori, Rajamani - AlternationforTermination
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);


void f(int d) {
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	int k = __VERIFIER_nondet_int();
	int z = 1;
	if (k > 1073741823) {
		return;
	}
	// ...
	L1:
	while (z < k) {
		z = 2 * z;
	}
	L2:
	while (x > 0 && y > 0) {
		// ...
		if (__VERIFIER_nondet_int()) {
			P1:
			x = x - d;
			y = __VERIFIER_nondet_int();
			z = z - 1;
		} else {
			y = y - d;
		}
	}
}

int main() {
	if (__VERIFIER_nondet_int()) {
		f(1);
	} else {
		f(2);
	}
}

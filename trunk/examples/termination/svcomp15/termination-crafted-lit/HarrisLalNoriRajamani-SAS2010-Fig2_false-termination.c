/*
 * Program from Fig.2 of
 * 2010SAS - Harris, Lal, Nori, Rajamani - AlternationforTermination
 * for k = 4 and 8 paths through foo.
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);


/*
 * Procedure that has 8 path through its body.
 */
int foo(void) {
	int y = __VERIFIER_nondet_int();
	if (__VERIFIER_nondet_int()) {
		if (__VERIFIER_nondet_int()) {
			if (__VERIFIER_nondet_int()) {
				y = 0;
			} else {
				y = 1;
			}
		} else {
			if (__VERIFIER_nondet_int()) {
				y = 2;
			} else {
				y = 3;
			}
		}
	} else {
		if (__VERIFIER_nondet_int()) {
			if (__VERIFIER_nondet_int()) {
				y = 4;
			} else {
				y = 5;
			}
		} else {
			if (__VERIFIER_nondet_int()) {
				y = 6;
			} else {
				y = 7;
			}
		}
	}
	return y;
}


int main() {
	int d = 1;
	int x = __VERIFIER_nondet_int();

	if (__VERIFIER_nondet_int()) {
		d = d - 1;
	}


	if (__VERIFIER_nondet_int()) {
		foo();
	}
	if (__VERIFIER_nondet_int()) {
		foo();
	}
	if (__VERIFIER_nondet_int()) {
		foo();
	}
	if (__VERIFIER_nondet_int()) {
		foo();
	}

	// I think there is a typo in the paper and the following
	// decrement can be omitted.
	if (__VERIFIER_nondet_int()) {
		d = d - 1;
	}

	while (x > 0) {
		x = x - d;
	}
	return 0;
}

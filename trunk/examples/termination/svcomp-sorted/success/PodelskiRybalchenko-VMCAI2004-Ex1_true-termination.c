/*
 * Program from Ex.1 of
 * 2004VMCAI - Podelski,Rybalchenko - A complete method for the synthesis of linear ranking functions
 *
 * Date: 2014
 * Author: Caterina Urban, Matthias Heizmann
 */

extern int __VERIFIER_nondet_int(void);

/**
 * Returns the absolut value of i. Assumes that can be no overflow.
 */
int absMathInteger(int i) {
	if (i >= 0) {
		return i;
	} else {
		return -i;
	}
}

int main() {
	int i = __VERIFIER_nondet_int();
	int j = __VERIFIER_nondet_int();
	while (i - j >= 1) {
		int nondetNat = absMathInteger(__VERIFIER_nondet_int());
		i = i - nondetNat;
		int nondetPos = absMathInteger(__VERIFIER_nondet_int()) + 1;
		j = j + nondetPos;
	}
	return 0;
}
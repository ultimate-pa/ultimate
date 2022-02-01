//#termcomp16-someonesaidyes
/*
 * Program from Ex.1 of
 * 2004VMCAI - Podelski,Rybalchenko - A complete method for the synthesis of linear ranking functions
 *
 * Date: 2014
 * Author: Caterina Urban, Matthias Heizmann
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i, j, nondetNat, nondetPos;
	i = __VERIFIER_nondet_int();
	j = __VERIFIER_nondet_int();
	while (i - j >= 1) {
        nondetNat = __VERIFIER_nondet_int();
        if (nondetNat < 0) {
            nondetNat = -nondetNat;
        }
		i = i - nondetNat;
		nondetPos = __VERIFIER_nondet_int();
        if (nondetPos < 0) {
            nondetPos = -nondetPos;
        }
        nondetPos = nondetPos + 1;
		j = j + nondetPos;
	}
	return 0;
}

//#termcomp16-someonesaidyes
/*
 * Program from Fig.1 of
 * 2013WST - Urban - Piecewise-Defined Ranking Functions
 *
 * Date: 12.12.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
	int x1;
	int x2;
	x1 = __VERIFIER_nondet_int();
	x2 = __VERIFIER_nondet_int();
    while (x1 <= 10) {
        x2 = 1000;
        while (x2 > 1) {
            x2 = x2 -1;
        }
        x1 = x1 + 1;
    }
    return 0;
}

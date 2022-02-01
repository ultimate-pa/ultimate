/*
 * Program from Fig.2 of
 * 2013WST - Urban - Piecewise-Defined Ranking Functions
 *
 * Date: 12.12.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x = __VERIFIER_nondet_int();
    while (x <= 10) {
        if (x > 6) {
            x = x + 2;
        }
    }
}

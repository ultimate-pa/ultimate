/*
 * Program from Fig.3 of
 * 2010SAS - Harris, Lal, Nori, Rajamani - AlternationforTermination
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);

int x;

void foo(void) {
	x--;
}


int main() {
	x = __VERIFIER_nondet_int();

	while (x > 0) {
		if (__VERIFIER_nondet_int()) {
			foo();
		} else {
			foo();
		}
	}
	return 0;
}

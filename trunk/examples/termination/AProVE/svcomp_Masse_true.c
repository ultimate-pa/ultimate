/*
 * Terminating Program
 * Damien Massé showed me this program
 *
 * Date: 18.12.2013
 * Author: urban@di.ens.fr
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x;
	while (x <= 1000) {
		if (__VERIFIER_nondet_int()) {
			x = - 2 * x + 2;
		} else {
			x = - 3 * x - 2;
		}
	}
}
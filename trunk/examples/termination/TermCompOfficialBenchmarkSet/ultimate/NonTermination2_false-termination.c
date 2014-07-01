/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int();

int main() {
	int x = __VERIFIER_nondet_int();
	while (x > 1) {
		int old_x = x;
		x = __VERIFIER_nondet_int();
		if (x < 2*old_x) {
			break;
		}
	}
	return 0;
}

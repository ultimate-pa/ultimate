/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int();

int main() {
	int i = __VERIFIER_nondet_int();
	int a[10];
	while (0 <= i && i < 10 && a[i] >= 0) {
		i = __VERIFIER_nondet_int();
		a[i] = 0;
	}
	return 0;
}

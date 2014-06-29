/*
 * Date: 2014-06-01
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(a[3], b[1+2], a[2+1]) = a[3]
 *
 */
extern int __VERIFIER_nondet_int(void);

int main() {
	int a[1048];
	while (a[1+2] >= 0) {
		a[3] = a[2+1] - 1;
	}
	return 0;
}

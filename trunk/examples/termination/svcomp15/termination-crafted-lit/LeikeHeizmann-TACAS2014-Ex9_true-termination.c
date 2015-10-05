/*
 * Program from Example 9 of
 * 2014TACAS - Leike, Heizmann - Ranking Templates for Linear Loops
 *
 * Date: 2014-06-29
 * Author: Jan Leike
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int q = __VERIFIER_nondet_int();
	int p = __VERIFIER_nondet_int();
	while (q > 0 && p > 0) {
		if (q < p) {
			q = q - 1;
		} else {
			if (p < q) {
				p = p - 1;
			} else {
				break;
			}
		}
	}
	return 0;
}

/*
 * Program from Example 1 of
 * 2014TACAS - Leike, Heizmann - Ranking Templates for Linear Loops
 *
 * Date: 2014-06-29
 * Author: Jan Leike
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int q = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	while (q > 0) {
		if (y > 0) {
			q = q - y - 1;
		} else {
			q = q + y - 1;
		}
	}
	return 0;
}

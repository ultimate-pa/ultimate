/*
 * Program from Example 5 of
 * 2014WST - Leike, Heizmann - Geometric Series as Nontermination Arguments for Linear Lasso Programs
 *
 * Date: 2014-06-29
 * Author: Jan Leike
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int a = __VERIFIER_nondet_int();
	int b = __VERIFIER_nondet_int();
	while (a >= 7) {
		int old_a = a;
		a = b;
		b = old_a + 1;
		// b = a + 1; is a typo in the paper
	}
	return 0;
}

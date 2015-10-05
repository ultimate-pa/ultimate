/*
 * Program from Figure 9 of
 * 2013ATVA - Heizmann, Hoenicke, Leike, Podelski - Linear Ranking for Linear Lasso Programs
 *
 * Date: 2014-06-29
 * Author: Jan Leike
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	int z = __VERIFIER_nondet_int();
	if (2*y < z) {
		return 0;
	}
	while (x >= 0 && z == 1) {
		x = x - 2*y + 1;
	}
	return 0;
}

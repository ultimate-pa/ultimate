/*
 * Program from Figure 2 of
 * 2013ATVA - Heizmann, Hoenicke, Leike, Podelski - Linear Ranking for Linear Lasso Programs
 *
 * Date: 2014-06-29
 * Author: Jan Leike
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int y = __VERIFIER_nondet_int();
	int x = y + 42;
	while (x >= 0) {
		y = 2*y - x;
		x = (y + x) / 2;
	}
	return 0;
}

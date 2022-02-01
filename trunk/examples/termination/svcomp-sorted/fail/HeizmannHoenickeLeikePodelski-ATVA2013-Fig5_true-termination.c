/*
 * Program from Figure 5 of
 * 2013ATVA - Heizmann, Hoenicke, Leike, Podelski - Linear Ranking for Linear Lasso Programs
 *
 * Date: 2014-06-29
 * Author: Jan Leike
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x = __VERIFIER_nondet_int();
	int y = 2;
	while (x >= 0) {
		x = x - y;
		y = (y + 1) / 2;
	}
	return 0;
}

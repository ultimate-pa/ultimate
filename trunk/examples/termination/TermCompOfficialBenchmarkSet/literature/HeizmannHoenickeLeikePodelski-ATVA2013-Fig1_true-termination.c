/*
 * Program from Figure 1 of
 * 2013ATVA - Heizmann, Hoenicke, Leike, Podelski - Linear Ranking for Linear Lasso Programs
 *
 * Date: 2014-06-29
 * Author: Jan Leike
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x = __VERIFIER_nondet_int();
	int y = 23;
	while (x >= 0) {
		x = x - y;
		y = y + 1;
	}
	return 0;
}

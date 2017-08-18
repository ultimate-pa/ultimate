//#termcomp16-someonesaidyes
/*
 * Program from Figure 6 of
 * 2013ATVA - Heizmann, Hoenicke, Leike, Podelski - Linear Ranking for Linear Lasso Programs
 *
 * Date: 2014-06-29
 * Author: Jan Leike
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x, y;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	while (x >= 0 && y >= 1) {
		x = x - y;
		y = __VERIFIER_nondet_int();
	}
	return 0;
}

//#termcomp16-someonesaidyes
/*
 * Program from Figure 4 of
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
	y = 23;
	while (x >= y) {
		x = x - 1;
	}
	return 0;
}

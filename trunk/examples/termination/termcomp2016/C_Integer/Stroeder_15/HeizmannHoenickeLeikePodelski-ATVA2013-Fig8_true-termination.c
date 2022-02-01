//#termcomp16-someonesaidyes
/*
 * Program from Figure 8 of
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
	if (2*y >= 1) {
    	while (x >= 0) {
	    	x = x - 2*y + 1;
	    }
	}
	return 0;
}

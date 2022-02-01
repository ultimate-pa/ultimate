//#termcomp16-someonesaidyes
/*
 * Program used in the experimental evaluation of the following paper.
 * 2008ESOP - Chawdhary,Cook,Gulwani,Sagiv,Yang - Ranking Abstractions
 *
 * Date: 2014
 * Author: Caterina Urban
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x, tx, y, ty, n;
	x = __VERIFIER_nondet_int();
	tx = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	ty = __VERIFIER_nondet_int();
	n = __VERIFIER_nondet_int();
	if (x + y >= 0) {
		while (x <= n && x >= 2 * tx + y && y >= ty + 1 && x >= tx + 1) {
			if (__VERIFIER_nondet_int() != 0) {
				tx = x;
				ty = y;
				x = __VERIFIER_nondet_int();
				y = __VERIFIER_nondet_int();
			} else {
				tx = x;
				x = __VERIFIER_nondet_int();
			}
		}
	}	
	return 0;
}

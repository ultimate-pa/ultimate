//#termcomp16-someonesaidyes
/*
 * Program used in the experimental evaluation of the following paper.
 * 2010SAS - Alias,Darte,Feautrier,Gonnord, Multi-dimensional Rankings, Program Termination, and Complexity Bounds of Flowchart Programs
 *
 * Date: 2014
 * Author: Caterina Urban
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x, y, n, b;
	n = __VERIFIER_nondet_int();
	b = __VERIFIER_nondet_int();
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	while (x >= 0 && 0 <= y && y <= n) {
		if (b == 0) {
			y = y + 1;
			if (__VERIFIER_nondet_int() != 0) {
				b = 1;
            }
		} else {
			y = y - 1;
			if (__VERIFIER_nondet_int() != 0) {
				x = x - 1;
				b = 0;
			}
		}
	}
	return 0;
}

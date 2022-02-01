//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
/*
 * Program used in the experimental evaluation of the following papers.
 * 2008ESOP - Chawdhary,Cook,Gulwani,Sagiv,Yang - Ranking Abstractions
 * 2010SAS - Alias,Darte,Feautrier,Gonnord, Multi-dimensional Rankings, Program 
 *           Termination, and Complexity Bounds of Flowchart Programs
 *
 * Date: 2014
 * Author: Caterina Urban
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x, y, tx;
	tx = __VERIFIER_nondet_int();
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	while (x >= y && tx >= 0) {
		if (__VERIFIER_nondet_int() != 0) {
			x = x - 1 - tx;
		} else {
			y = y + 1 + tx;
		}
	}
	return 0;
}

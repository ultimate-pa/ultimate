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
    int m, n, v1, v2;
	n = __VERIFIER_nondet_int();
	m = __VERIFIER_nondet_int();
	if (n >= 0 && m > 0) {
		v1 = n;
		v2 = 0;
		while (v1 > 0) {
			if (v2 < m) {
				v2 = v2 + 1;
				v1 = v1 - 1;
			} else {
				v2 = 0;
			}
		}
	}
	return 0;
}

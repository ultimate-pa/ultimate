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
    int i, j, N;
	j = __VERIFIER_nondet_int();
	N = __VERIFIER_nondet_int();
	i = N;
	while (i > 0) {
		if (j > 0) {
			j = j - 1;
		} else {
			j = N;
			i = i - 1;
		}
	}
	return 0;
}

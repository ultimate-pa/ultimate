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
    int r, da, db, temp;
	r = __VERIFIER_nondet_int();
	if (r >= 0) {
		da = 2 * r;
		db = 2 * r;
		while (da >= r) {
			if (__VERIFIER_nondet_int() != 0) {
				da = da - 1;
			} else {
				temp = da;
				da = db - 1;
				db = da;
			}
		}
	}
	return 0;
}

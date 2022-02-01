/*
 * Program used in the experimental evaluation of the following paper.
 * 2010SAS - Alias,Darte,Feautrier,Gonnord, Multi-dimensional Rankings, Program Termination, and Complexity Bounds of Flowchart Programs
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int tx = __VERIFIER_nondet_int();
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	while (x >= y && tx >= 0) {
		if (__VERIFIER_nondet_int()) {
			x = x - 1 - tx;
		} else {
			y = y + 1 + tx;
		}
	}
	return 0;
}
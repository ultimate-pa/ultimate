/*
 * Program used in the experimental evaluation of the following paper.
 * 2010SAS - Alias,Darte,Feautrier,Gonnord, Multi-dimensional Rankings, Program Termination, and Complexity Bounds of Flowchart Programs
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	int z = __VERIFIER_nondet_int();
	int tx = __VERIFIER_nondet_int();
	while (x >= y && x <= tx + z) {
		if (__VERIFIER_nondet_int()) {
			z = z - 1;
			tx = x;
			x = __VERIFIER_nondet_int();
		} else {
			y = y + 1;
		}
	}
	return 0;
}
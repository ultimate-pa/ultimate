/*
 * Program used in the experimental evaluation of the following paper.
 * 2010SAS - Alias,Darte,Feautrier,Gonnord, Multi-dimensional Rankings, Program Termination, and Complexity Bounds of Flowchart Programs
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x = 0, y = 100, z = __VERIFIER_nondet_int();
	while (x < 40) {
		if (z == 0) {
			x = x + 1;
		} else {
			x = x + 2;
		}
	}
	return 0;
}
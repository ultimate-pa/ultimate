/*
 * Program used in the experimental evaluation of the following paper.
 * 2010SAS - Alias,Darte,Feautrier,Gonnord, Multi-dimensional Rankings, Program Termination, and Complexity Bounds of Flowchart Programs
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int n = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	int x = n;
	if (x >= 0) {
		while (x >= 0) {
			y = 1;
			if (y < x) {
				while (y < x)
					y = 2*y;
			}
			x = x - 1;
		}
	}
	return 0;
}
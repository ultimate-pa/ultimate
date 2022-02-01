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
	while (x >= 2) {
		x--; y = y + x;
		while (y >= x + 1 && __VERIFIER_nondet_int()) {
			y--;
			while (y >= x + 3 && __VERIFIER_nondet_int()) {
				x++; y = y - 2;
			}
			y--;
		}
		x--; y = y - x;
	}
	return 0;
}
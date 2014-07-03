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
	int b = __VERIFIER_nondet_int();
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	while (x >= 0 && 0 <= y && y <= n) {
		if (b == 0) {
			y++;
			if (__VERIFIER_nondet_int())
				b = 1;
		} else {
			y--;
			if (__VERIFIER_nondet_int()) {
				x--;
				b = 0;
			}
		}
	}
	return 0;
}
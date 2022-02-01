/*
 * Program used in the experimental evaluation of the following paper.
 * 2010SAS - Alias,Darte,Feautrier,Gonnord, Multi-dimensional Rankings, Program Termination, and Complexity Bounds of Flowchart Programs
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int i = __VERIFIER_nondet_int();
	int x = __VERIFIER_nondet_int();
	int n = __VERIFIER_nondet_int();
	int b = __VERIFIER_nondet_int();
	int t;
	if (b >= 1)
		t = 1;
	else
		t = -1;
	while (x <= n) {
		if (b >= 1) {
			x = x + t;
		} else {
			x = x - t;
		}
	}
	return 0;
}
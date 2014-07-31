/*
 * Program used in the experimental evaluation of the following paper.
 * 2010SAS - Alias,Darte,Feautrier,Gonnord, Multi-dimensional Rankings, Program Termination, and Complexity Bounds of Flowchart Programs
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int a, x, max = __VERIFIER_nondet_int();
	if (max > 0) {
		a = 0;
		x = 1;
		while (x <= max) {
			if (__VERIFIER_nondet_int())
				a = a + 1;
			else
				a = a - 1;
			x = x + 1;
		}
	}
	return 0;
}
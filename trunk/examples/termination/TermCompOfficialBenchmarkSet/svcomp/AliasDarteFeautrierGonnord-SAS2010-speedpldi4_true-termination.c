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
	int m = __VERIFIER_nondet_int();
	int i;
	if (m > 0 && n > m) {
		i = n;
		while (i > 0) {
			if (i < m)
				i--;
			else
				i -= m;
		}
	}
	return 0;
}
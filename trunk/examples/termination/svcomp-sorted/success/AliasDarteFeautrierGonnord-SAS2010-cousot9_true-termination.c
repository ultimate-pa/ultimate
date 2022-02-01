/*
 * Program used in the experimental evaluation of the following paper.
 * 2010SAS - Alias,Darte,Feautrier,Gonnord, Multi-dimensional Rankings, Program Termination, and Complexity Bounds of Flowchart Programs
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int j = __VERIFIER_nondet_int();
	int N = __VERIFIER_nondet_int();
	int i = N;
	while (i > 0) {
		if (j > 0) {
			j--;
		} else {
			j = N;
			i--;
		}
	}
	return 0;
}
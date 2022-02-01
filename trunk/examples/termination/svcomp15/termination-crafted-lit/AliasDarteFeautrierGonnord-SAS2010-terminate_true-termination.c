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
	int j = __VERIFIER_nondet_int();
	int k = __VERIFIER_nondet_int();
	int ell;
	while (i <= 100 && j <= k) {
		ell = i;
		i = j;
		j = ell + 1;
		k--;
	}
	return 0;
}
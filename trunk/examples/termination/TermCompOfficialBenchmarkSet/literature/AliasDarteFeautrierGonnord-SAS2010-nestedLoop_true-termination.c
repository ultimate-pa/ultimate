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
	int n = __VERIFIER_nondet_int();
	int m = __VERIFIER_nondet_int();
	int N = __VERIFIER_nondet_int();
	if (0 <= n && 0 <= m && 0 <= N) {
		i = 0;
		while (i < n) {
			j = 0;
			while (j < m) {
				j += 1;
				k = i;
				while (k < N)
					k += 1;
				i = k;
			}
			i++;
		}
	}
	return 0;
}
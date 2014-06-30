/*
 * Program used in the experimental evaluation of the following paper.
 * 2010SAS - Alias,Darte,Feautrier,Gonnord, Multi-dimensional Rankings, Program Termination, and Complexity Bounds of Flowchart Programs
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int N = __VERIFIER_nondet_int();
	int j;
	int i = N;
	while (i > 0) {
		j = N;
		while (j > 0)
			j--;
		i--;
	}
	return 0;
}
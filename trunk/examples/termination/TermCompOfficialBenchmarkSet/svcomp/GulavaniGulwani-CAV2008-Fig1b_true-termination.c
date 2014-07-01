/*
 * Program from Fig.1b of
 * 2008CAV - Gulavani,Gulwani - A Numerical Abstract Domain Based on Expression Abstraction and Max Operator with Application in Timing Analysis
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x = __VERIFIER_nondet_int();
	int i = __VERIFIER_nondet_int();
	int n = __VERIFIER_nondet_int();
	int m = __VERIFIER_nondet_int();
	while (x < n) {
		i = i + 1;
		x = x + 1;
	}
	while (x < m) {
		i = i + 1;
		x = x + 1;
	}
	return 0;
}
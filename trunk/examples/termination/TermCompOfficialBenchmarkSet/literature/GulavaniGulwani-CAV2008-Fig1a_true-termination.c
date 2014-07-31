/*
 * Program from Fig.1a of
 * 2008CAV - Gulavani,Gulwani - A Numerical Abstract Domain Based on Expression Abstraction and Max Operator with Application in Timing Analysis
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	int z = __VERIFIER_nondet_int();
	int i = __VERIFIER_nondet_int();
	while (x < y) {
		i = i + 1;
		if (z > x) {
			x = x + 1;
		} else {
			z = z + 1;
		}
	}
	return 0;
}
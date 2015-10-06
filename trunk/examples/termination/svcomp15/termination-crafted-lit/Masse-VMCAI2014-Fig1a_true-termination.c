/*
 * Program from Fig.1a of
 * 2014VMCAI - Massé - Policy Iteration-Based Conditional Termination and Ranking Functions
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int a = __VERIFIER_nondet_int();
	int b = __VERIFIER_nondet_int();
	while (a >= 0) {
		a = a + b;
		if (b >= 0) {
			b = -b - 1;
		} else {
			b = -b;
		}
	}
	return 0;
}
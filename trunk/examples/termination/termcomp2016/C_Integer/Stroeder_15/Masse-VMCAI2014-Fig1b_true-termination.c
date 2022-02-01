/*
 * Program from Fig.1b of
 * 2014VMCAI - Massé - Policy Iteration-Based Conditional Termination and Ranking Functions
 *
 * Date: 2014
 * Author: Caterina Urban
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
	int x;
    x = __VERIFIER_nondet_int();
	while (x <= 100) {
		if (__VERIFIER_nondet_int() != 0) {
			x = -2*x + 2;
		} else {
			x = -3*x - 2;
		}
	}
	return 0;
}

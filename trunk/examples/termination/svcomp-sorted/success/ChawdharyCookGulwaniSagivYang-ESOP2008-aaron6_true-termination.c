/*
 * Program used in the experimental evaluation of the following paper.
 * 2008ESOP - Chawdhary,Cook,Gulwani,Sagiv,Yang - Ranking Abstractions
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int x = __VERIFIER_nondet_int();
	int tx = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	int ty = __VERIFIER_nondet_int();
	int n = __VERIFIER_nondet_int();
	if (x + y >= 0) {
		while (x <= n && x >= 2 * tx + y && y >= ty + 1 && x >= tx + 1) {
			if (__VERIFIER_nondet_int()) {
				tx = x;
				ty = y;
				x = __VERIFIER_nondet_int();
				y = __VERIFIER_nondet_int();
			} else {
				tx = x;
				x = __VERIFIER_nondet_int();
			}
		}
	}	
	return 0;
}
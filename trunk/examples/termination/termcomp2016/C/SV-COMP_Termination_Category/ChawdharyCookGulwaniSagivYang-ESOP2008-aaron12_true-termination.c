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
	int y = __VERIFIER_nondet_int();
	int z = __VERIFIER_nondet_int();
	while (x >= y) {
		if (__VERIFIER_nondet_int()) {
			x = x + 1;
			y = y + x;
		} else {
			x = x - z;
			y = y + (z * z);
			z = z - 1;
		}
	}
	return 0;
}
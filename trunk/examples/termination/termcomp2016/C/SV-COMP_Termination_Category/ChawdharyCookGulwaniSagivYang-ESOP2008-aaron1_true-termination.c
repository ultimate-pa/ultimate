/*
 * Program used in the experimental evaluation of the following paper.
 * 2008ESOP - Chawdhary,Cook,Gulwani,Sagiv,Yang - Ranking Abstractions
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int i = __VERIFIER_nondet_int();
	int j = __VERIFIER_nondet_int();
	int an = __VERIFIER_nondet_int();
	int bn = __VERIFIER_nondet_int();
	while ((an >= i && bn >= j) || (an >= i && bn <= j) || (an <= i && bn >= j)) {
		if (an >= i && bn >= j) {
			if (__VERIFIER_nondet_int()) {
				j = j + 1;
			} else {
				i = i + 1;
			}
		} else if (an >= i && bn <= j) {
			i = i + 1;
		} else if (an <= i && bn >= j) {
			j = j + 1;
		}
	}
	return 0;
}
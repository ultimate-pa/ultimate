/*
 * Program used in the experimental evaluation of the following paper.
 * 2008ESOP - Chawdhary,Cook,Gulwani,Sagiv,Yang - Ranking Abstractions
 *
 * Date: 2014
 * Author: Caterina Urban
 */

extern int __VERIFIER_nondet_int(void);

int main() {
	int N = 10, x = 0, y = 0, i = 0, r;
	while (i < N) {
		i = i + 1;
		r = __VERIFIER_nondet_int();
		if (r >= 0 && r <= 3) {
			if (r == 0)
				x = x + 1;
			else if (r == 1)
				x = x - 1;
			else if (r == 2)
				y = y + 1;
			else if (r == 3)
				y = y - 1;
		}
	}
	return 0;
}
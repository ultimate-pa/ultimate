/*
 * Program from Fig.1 of
 * 2013FMCAD - Larraz,Oliveras,Rodriguez-Carbonell,Rubio - Proving Termination of Imperative Programs Using Max-SMT
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);


int main() {
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	int z = __VERIFIER_nondet_int();
	// continue only for values where there won't be any overflow or underflow
	// on systems where sizeof(int)=4 holds.
	if (x > 10000 || x < -10000 || y > 10000 || z > 10000) {
		return 0;
	}
	while (y >= 1) {
		x--;
		while (y < z) {
			x++;
			z--;
		}
		y = x + y;
	}
	return 0;
}



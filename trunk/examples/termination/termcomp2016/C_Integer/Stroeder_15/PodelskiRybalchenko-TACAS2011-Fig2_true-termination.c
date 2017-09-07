//#termcomp16-someonesaidyes
/*
 * Program from Fig.2 of
 * 2011TACAS - Podelski,Rybalchenko - Transition Invariants and Transition Predicate Abstraction for Program Termination
 *
 * Date: 2014
 * Author: Caterina Urban
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x, y;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	while (x >= 0) {
		y = 1;
		while (y < x) {
			y = y + 1;
		}
		x = x - 1;
	}
	return 0;
}

//#termcomp16-someonesaidyes
/*
 * Program from Fig.2 of
 * 2004LICS - Podelski, Rybalchenko - Transition Invariants
 * Program from Fig.3 of
 * 2011TACAS - Podelski,Rybalchenko - Transition Invariants and Transition 
 *                                    Predicate Abstraction for Program 
 *                                    Termination
 *
 * Date: 2014
 * Author: Caterina Urban, Matthias Heizmann
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x, y, oldx, oldy;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	while (x > 0 && y > 0) {
		oldx = x;
		oldy = y;
		if (__VERIFIER_nondet_int() != 0) {
			x = oldx - 1;
			y = oldx;
		} else {
			x = oldy - 2;
			y = oldx + 1;
		}
	}
	return 0;
}

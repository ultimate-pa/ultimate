//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
/*
 * Terminating program that has no linear lexicographic ranking function.
 * The program chooses nondeterministically the variable x or y and assigns to
 * it the result of   minimum(x,y)-1
 * The term   minimum(x,y)  is a ranking function for this program.
 *
 * Amir Ben-Amram (TelAviv) showed me this program when we met in Perpignan at
 * SAS 2010.
 *
 * Date: 1.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
	int x;
	int y;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
    while (x > 0 && y > 0) {
    	if (__VERIFIER_nondet_int() != 0) {
    		if (x<y) {
    			y = x - 1;
    		} else {
    			y = y - 1;
    		}
    		x = __VERIFIER_nondet_int();
    	} else {
    		if (x<y) {
    			x = x - 1;
    		} else {
    			x = y - 1;
    		}
    		y = __VERIFIER_nondet_int();
    	}
    }
    return 0;
}

//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
/*
 * Date: 2011-12-11
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(x, y) = x
 * provided with the supporting invariant y >= 1.
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
    int x, y;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	if (y >= 1) {
    	while (x >= 0) {
	    	x = x - y;
	    }
	}
	return 0;
}

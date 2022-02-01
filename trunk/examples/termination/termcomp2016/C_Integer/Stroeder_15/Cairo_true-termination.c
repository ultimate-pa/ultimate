//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
/*
 * Ranking function f(x) = x 
 * with supporting invariant x >= 0
 * Makes use of disjunctions in the loop. 
 * Terminates only over the integers not over rationals.
 *
 * Date: 2012-04-06
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
    int x;
	x = __VERIFIER_nondet_int();
	if (x > 0) {
    	while (x != 0) {
	    	x = x - 1;
	    }
	}
	return 0;
}

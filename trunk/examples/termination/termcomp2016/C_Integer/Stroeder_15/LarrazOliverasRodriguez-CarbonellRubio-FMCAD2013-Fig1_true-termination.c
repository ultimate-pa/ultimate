//#termcomp16-someonesaidyes
/*
 * Program from Fig.1 of
 * 2013FMCAD - Larraz,Oliveras,Rodriguez-Carbonell,Rubio - Proving Termination of Imperative Programs Using Max-SMT
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x, y, z;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	z = __VERIFIER_nondet_int();
	// continue only for values where there won't be any overflow or underflow
	// on systems where sizeof(int)=4 holds.
	if (x <= 10000 && x >= -10000 && y <= 10000 && z <= 10000) {
	    while (y >= 1) {
		    x = x - 1;
		    while (y < z) {
			    x = x + 1;
			    z = z - 1;
		    }
	    	y = x + y;
    	}
	}
	return 0;
}

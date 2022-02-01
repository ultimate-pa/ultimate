//#termcomp16-someonesaidyes
/*
 * Program from Fig.1 of
 * 2005CAV - Bradley,Manna,Sipma - Linear Ranking with Reachability
 *
 * Date: 12.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int y1, y2;
	y1 = __VERIFIER_nondet_int();
	y2 = __VERIFIER_nondet_int();
	if (y1 > 0 && y2 > 0) {
    	while (y1 != y2) {
	    	if (y1 > y2) {
		    	y1 = y1 - y2;
    		} else {
	    		y2 = y2 - y1;
		    }
	    }
	}
	return 0;
}

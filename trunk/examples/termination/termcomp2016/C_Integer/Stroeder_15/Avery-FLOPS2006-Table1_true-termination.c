//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
/*
 * Program from Table 1 of
 * 2006FLOPS - James Avery - Size-Change Termination and Bound Analysis
 *
 * Date: 18.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int x, y, z, i;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	z = 0;
	i = x;
	if (y > 0 && x > 0) {
    	while (i > 0) {
	    	i = i - 1;
		    z = z + 1;
	    }
    	while (i < y) {
	    	i = i + 1;
		    z = z - 1;
	    }
	}
	return 0;
}

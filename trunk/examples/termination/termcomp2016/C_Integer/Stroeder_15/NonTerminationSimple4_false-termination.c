//#termcomp16-someonesaidno
//#termcomp16-someonesaidno
/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 *
 * Does not terminate for y >= 5.
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
    int x, y;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	if (y >= 5) {
	    while (x >= 0) {
		    y = y - 1;
    	}
    }
	return 0;
}

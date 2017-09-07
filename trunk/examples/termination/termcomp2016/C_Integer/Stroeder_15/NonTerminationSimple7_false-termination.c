//#termcomp16-someonesaidno
//#termcomp16-someonesaidno
/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
    int c, x;
	x = __VERIFIER_nondet_int();
	c = __VERIFIER_nondet_int();
	if (c == 0) {
	    while (x >= 0) {
		    x = x + c;
	    }
    }
	return 0;
}

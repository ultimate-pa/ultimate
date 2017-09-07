//#termcomp16-someonesaidno
//#termcomp16-someonesaidno
/*
 * Date: 2013-12-16
 * Author: leike@informatik.uni-freiburg.de
 *
 * Does not terminate for c >= 0.
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
	int c, x;
    c = __VERIFIER_nondet_int();
	x = __VERIFIER_nondet_int();
	while (x >= 0) {
		x = x + c;
	}
    return 0;
}

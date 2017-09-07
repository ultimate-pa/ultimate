//#termcomp16-someonesaidno
//#termcomp16-someonesaidno
/*
 * Date: 2013-12-16
 * Author: leike@informatik.uni-freiburg.de
 *
 * Simple example for non-termination
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
	int x;
    x = __VERIFIER_nondet_int();
	while (x >= 0) {
		x = x + 1;
	}
    return 0;
}

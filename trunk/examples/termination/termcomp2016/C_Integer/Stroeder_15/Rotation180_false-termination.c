//#termcomp16-someonesaidno
//#termcomp16-someonesaidno
/*
 * Date: 2013-12-16
 * Author: leike@informatik.uni-freiburg.de
 *
 * Rotates x and y by 90 degrees
 * Does not terminate.
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main ()
{
    int oldx;
	int x;
	int y;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	while (true) {
        oldx = x;
		x = -y;
		y = oldx;
	}
	return 0;
}

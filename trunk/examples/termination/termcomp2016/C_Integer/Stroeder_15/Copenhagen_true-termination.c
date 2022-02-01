//#termcomp16-someonesaidyes
/*
 * Date: 2012-02-18
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
    int x, y, oldx;
	x = __VERIFIER_nondet_int();
	y = __VERIFIER_nondet_int();
	while (x >= 0 && y >= 0) {
		oldx = x;
		x = y - 1;
		y = oldx - 1;
	}
	return 0;
}

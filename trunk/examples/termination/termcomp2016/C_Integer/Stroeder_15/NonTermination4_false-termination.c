//#termcomp16-someonesaidno
/*
 * Date: 2013-12-20
 * Author: leike@informatik.uni-freiburg.de
 *
 * Difficult example for non-termination
 *
 * y = x^log_2(3)
 */
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
    int x, y;
	x = 1;
	y = 1;
	while (x >= 0) {
		x = 2*x;
		y = 3*y;
	}
	return 0;
}

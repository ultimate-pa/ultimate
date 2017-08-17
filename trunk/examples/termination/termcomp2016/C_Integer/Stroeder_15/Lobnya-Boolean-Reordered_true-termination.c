//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
/*
 * Date: 2013-07-10
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(x) = x
 *
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main ()
{
    int x, b;
	x = __VERIFIER_nondet_int();
	b = __VERIFIER_nondet_int();
	while (b != 0) {
		b = __VERIFIER_nondet_int();
		x = x - 1;
        if (x >= 0) {
            b = 1;
        } else {
            b = 0;
        }
	}
	return 0;
}

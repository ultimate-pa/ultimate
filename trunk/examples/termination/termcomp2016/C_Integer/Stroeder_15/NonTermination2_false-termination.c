//#termcomp16-someonesaidno
//#termcomp16-someonesaidno
/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 *
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
	int x, oldx;
    x = __VERIFIER_nondet_int();
	while (x > 1 && x >= 2*oldx) {
		oldx = x;
		x = __VERIFIER_nondet_int();
	}
	return 0;
}

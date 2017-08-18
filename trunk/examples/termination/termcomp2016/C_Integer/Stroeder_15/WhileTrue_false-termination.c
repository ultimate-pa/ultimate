//#termcomp16-someonesaidno
//#termcomp16-someonesaidno
/*
 * Date: 2013-12-16
 * Author: leike@informatik.uni-freiburg.de
 *
 * Very simple example for non-termination
 */
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
	while (true) {
		// do nothing
	}
	return 0;
}

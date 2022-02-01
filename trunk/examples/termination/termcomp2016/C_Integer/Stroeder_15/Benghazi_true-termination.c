//#termcomp16-someonesaidyes
/*
 * Date: 18.11.2012
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Has ranking function f(x,d1,d2)=x for the invariant
 * d1 >=1 /\ d2>=1.
 * 
 * This lasso program has a 2-phase ranking function.
 *
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main()
{
    int x, d1, d2, d1old;
	d1 = 73;
	d2 = 74;
	x = __VERIFIER_nondet_int();
	while (x >= 0) {
		x = x - d1;
		d1old = d1;
		d1 = d2 + 1;
		d2 = d1old + 1;
	}
	return 0;
}

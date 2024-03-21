//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-07-31
 *
 * Shows that our Trace Interpolation also works with floats.
 * 
 * Using the SP-based technique, we obtain roughly the following invariant
 * for the second loop.
 * exists y. x = y + 1.0 /\ y >=0
 * We do not have any quantifier elimination procedure for this formula.
 * However, since Z3 can handle quantifiers we are able to show that
 * this invariant is inductive.
 *
 */


extern double __VERIFIER_nondet_double(void);
extern double __VERIFIER_nondet_int(void);


int main() {
	double x = __VERIFIER_nondet_double();
	
	if (x >= 0.0) {
		while (__VERIFIER_nondet_int()) {
			x = x + 1.0;
		}
		x = x + 1.0;
		while (__VERIFIER_nondet_int()) {
			x = x + 1.0;
		}
		//@ assert x > 0.0;
	}
    return 0;
}

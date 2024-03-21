//#Safe
/* Simple examples in which we have a combination of 
 * - floats and
 * - bvadd with more than two arguments.
 * Floats make sure that we use MathSAT in WOLF refinement strategy,
 * bvadd with more than two arguments lets MathSAT crash.
 * K
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-05-23
 * 
 */
extern void __VERIFIER_error(void);
extern int __VERIFIER_nondet_int(void);

int main(void) {
	float f = 1.0;
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	if (x + y + 1 == 23) {
		if (x + y + 1 == 23 && f == 1.0) {
			// everything fine
		} else {
			__VERIFIER_error();
		}
	}
	return 0;
}

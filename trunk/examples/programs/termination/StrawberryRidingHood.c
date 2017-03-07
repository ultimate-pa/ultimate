//#rTermination
/*
 * Does not have a linear lexicographic ranking function.
 * The absolute value abs(y) is a ranking function that
 * shows termination.
 * 
 * Date: 2017-03-03
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int();

int main() {
	int y = __VERIFIER_nondet_int();
	
	// enter only if y is odd
	if (y % 2) {
		// loop until y is -1, 0, or 1.
		while ((y / 2) != 0) {
			// since, the C semantics of modulo is rounding towards zero, 
			// the expression (y % 2) implements the sign function
			y = 2 * (y % 2);
		}
	}
    return 0;
}

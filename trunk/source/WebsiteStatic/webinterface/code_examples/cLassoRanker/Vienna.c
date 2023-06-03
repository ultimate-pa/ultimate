// #Termination
/* Date: 2014-07-18 
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Proving termination of this program is very difficult, because a and b
 * are increasing at "different speeds".
 * 
 * Example that I discussed with Albert, Caterina, Carsten, Jürgen, Marc 
 * and Thomas on the blackboard at the WST 2014.
 * 
 * Later I discussed it with Amir and Samir via email.
 * They were able to prove that this program does not have a 
 * disjuctive well-founded transition invariant where each disjunct is
 * defined by a linear term.
 * 
 * A ranking function for this program is to the quotient a/b.
 * 
 */

int main() {
	int a, b;
	while (a >= b && a >= 1 && b >= 1) {
		a = 2*a;
		b = 3*b;
	}
	return 0;
}
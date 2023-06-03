//#rNonTermination
/*
 * Date: 04.01.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * From Amir M. Ben-Amram and Samir Genaim,
 * Ranking Functions for Linear-Constraint Loops.
 * POPL 2013
 *
 * Integer hull of loop of Example 3.20. (two assumes added)
 *
 * Does not terminate over the reals.
 * Has linear ranking function f(x1,x2) = x1 + x2 - 1 over the integers.
 * Loop is not integral.
 */

procedure main() returns () {
    var x1, x2: int;
    var x1old, x2old: int;
    
    assume(true);
    while (4*x1 >= x2 && x2 >= 1) {
        x1old := x1;
        havoc x1;
        assume(5*x1 <= 2*x1old + 1);
        assume(5*x1 >= 2*x1old - 3);
        assume(-x1old + x1 <= -1);
        assume(x1old - 3*x1 <= 1);
    }
}


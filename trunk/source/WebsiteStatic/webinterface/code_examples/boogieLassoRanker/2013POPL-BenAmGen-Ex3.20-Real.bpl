//#rNonTerminationDerivable
/*
 * Date: 2014-03-17
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * From Amir M. Ben-Amram and Samir Genaim,
 * Ranking Functions for Linear-Constraint Loops.
 * POPL 2013
 *
 * Does not terminate over the reals.
 * Has linear ranking function f(x1,x2)=x1+x2-1 over the integers.
 * Loop is not integral.
 */

procedure main() returns () {
    var x1, x2: real;
    while (0.0 - x1 + x2 <= 0.0 && 0.0 - x1 - x2 + 1.0 <= 0.0) {
        x2 := x2 - 2.0*x1 + 1.0;
    }
}


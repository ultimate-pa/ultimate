//#rTermination
/*
 * Date: 04.01.2013
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
    var x1, x2: int;
    while (-x1 + x2 <= 0 && -x1 - x2 <= -1) {
        x2 := x2 - 2*x1 + 1;
    }
}


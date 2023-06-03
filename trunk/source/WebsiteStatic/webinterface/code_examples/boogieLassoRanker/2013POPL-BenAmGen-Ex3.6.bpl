//#rTerminationDerivable
/*
 * Date: 04.01.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * From Amir M. Ben-Amram and Samir Genaim,
 * Ranking Functions for Linear-Constraint Loops.
 * POPL 2013
 *
 * Does not have a linear ranking function.
 */

procedure main() returns () {
    var x1, x2: int;
    while (x1 >= 0) {
        x1 := x1 + x2;
        x2 := x2 - 1;
    }
}


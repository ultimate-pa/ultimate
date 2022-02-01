//#rNonTerminationDerivable
/*
 * Date: 2014-03-19
 * Author: leike@informatik.uni-freiburg.de
 *
 * Test case for the correct handling of booleans.
 * Needs boolean support in the nontermination analysis.
 *
 */

procedure SyntaxSupportBooleans4() returns (b: bool, x : int)
{
    assume(b);
    while (x >= 0) {
        if (b) {
          x := x + 2;
        }
        x := x - 1;
    }
}

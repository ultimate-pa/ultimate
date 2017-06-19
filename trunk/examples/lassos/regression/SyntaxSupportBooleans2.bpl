//#rTerminationDerivable
/*
 * Date: 2014-03-19
 * Author: leike@informatik.uni-freiburg.de
 *
 * Test case for the correct handling of booleans
 *
 * f(x) = (b ? 1 : 0) is a ranking function
 */

// If we do not have the following useless variable
// the backtranslation of the ranking function fails
// because the BoogieAST does not know the type int.
var someInt:int;

procedure SyntaxSupportBooleans2() returns (b: bool)
{
    assume(b);
    while (b) {
        b := false;
    }
}

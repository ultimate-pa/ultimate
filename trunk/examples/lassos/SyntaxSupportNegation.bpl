//#rTerminationDerivable
/*
 * Date: 2012-04-02
 * Author: leike@informatik.uni-freiburg.de
 *
 * Test case for the correct handling of negations
 */

procedure SyntaxSupportNegation() returns (x: int)
{
  while (true) {
    assume(!(x < 0));
    x := x - 1;
  }
}

//#rTerminationDerivable
/*
 * Date: 2012-04-02
 * Author: leike@informatik.uni-freiburg.de
 *
 * Test case for the correct handling of disjunctions in the loop condition
 */

procedure SyntaxSupportDisjunction1(a: int, b: int, c: int) returns (x: int)
{
  while ((a >= 0 || b >= 0 || c >= 0) && x >= 0) {
    x := x - 1;
  }
}

//#rTerminationDerivable
/*
 * Date: 2013-12-29
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * One test case for the correct handling the if-then-else operator.
 */

var x,y:int;

procedure SyntaxSupportDivision1() returns ()
modifies x,y;
{
  y := 1;
  while (x >= 0) {
    x := x - (if y == 0 then 0 else 1);
  }
}

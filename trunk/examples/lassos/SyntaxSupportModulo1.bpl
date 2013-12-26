//#rTerminationDerivable
/*
 * Date: 2013-12-26
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * One test case for the correct handling of modulo
 */

var x,y:int;

procedure SyntaxSupportDivision1() returns ()
modifies x,y;
{
  y := 0;
  while (y >= 0) {
    x := x % 2;
	y := -1 - x;
  }
}

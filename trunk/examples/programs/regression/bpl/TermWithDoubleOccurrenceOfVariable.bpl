//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * 15.5.2012
 *
 */

procedure proc()
{
  var x, y: int;

  x := 1;
  y := x+x;
  assert(y == 2);
}


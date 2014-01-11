//#Safe
/*
 * Date: 8.3.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Version of SAS09paper example with reals instead of integers.
 */

procedure SAS09paper()
{
  var x, y: real;

  x := 0.0;
  y := 0.0;

  while (*) {
    x := x + 1.0;
  }

  assert(x != 0.0-1.0);
  assert(y != 0.0-1.0);
}


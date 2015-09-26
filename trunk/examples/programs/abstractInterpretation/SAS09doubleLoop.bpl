//#Safe
/*
 * Author: ermis@informatik.uni-freiburg.de
 *      heizmann@informatik.uni-freiburg.de
 *
 * Enlargement of TraceAbstrEx.bpl by another loop.
 */

procedure SAS09paper()
{
  var x, y: int;

  x := 0;
  y := 0;

  while (*) {
    x := x + 1;
  }

  while (*) {
    assert(x != -1);
    assert(y != -1);
    y := y + 1;
  }
  assert(x != -1);
  assert(y != -1);
}


//#mSafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Simple Program which is correct with respect to assertions.
 * In order to proof correctness one has to infer loop invariants e.g. x>=0
 *
 * The example is taken from our SAS'09 paper "Refinement of Trace Abstraction".
 * http://www.springerlink.com/content/d372357375t64146/fulltext.pdf
 *
 */

procedure SAS09paper()
{
  var x, y, z: int;

  assume 5*x==7*z;
  assume z >= 2;
  havoc z;
  x := x-2;
  y := 0;

  while (*) {
    x := x + 1;
  }

  assert(x != -1);
  assert(y != -1);
}


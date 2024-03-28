//#rTerminationDerivable
/*
 * Date: 2015-12-04
 * Author: podelski@informatik.uni-freiburg.de
 *
 * Ranking function: f(x, y) = if i > 0 then x else y
 * Needs the inductive invariant i != 0.
 */

procedure main() returns (x : int, y : int)
{
  var i : int;
  assume(i != 0);
  while (x > 0 && y > 0) {
    assume(i != 0);
    x := x - i;
    y := y + i;
  }
}


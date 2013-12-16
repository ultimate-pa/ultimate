//#rTerminationDerivable
/*
 * Variant of the yPositive example with two termination arguments,
 * one over the integers, one over the reals.
 * 
 * Has linear Ranking function x 
 * with non-decreasing linear supporting invariant y>=1
 * Has linear Ranking function z 
 * with non-decreasing linear supporting invariant w>=1
 * 
 * Date: 19.01.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main() returns ()
{
  var x, y: int;
  var z, w: real;
  w := 23.0;
  y := 23;
  while (x >= 0 && z >= 0.0) {
    x := x - y;
    y := y + 1;
    z := z - w;
    w := w + 1.0;
  }
}


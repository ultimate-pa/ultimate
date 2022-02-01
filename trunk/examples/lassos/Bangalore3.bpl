//#rTerminationDerivable
/*
 * Date: 15.11.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(x, c) = x
 * provided with the supporting invariant c > 0.
 * Reveals Bugs in revision 7508
 * - no ranking function is found for linear template
 * - if we comment the line "c := c" the ranking function f(x) = 1*x - 1 is
 *   found with two times the supporting invariant 1*c >= 0. But only c>0 is
 *   a valid supporting invariant.
 */

procedure Bangalore(y: int) returns (x: int)
{
  var c: int;
  assume(c >= 42);
  while (x >= 23) {
    x := x - c;
    c := c;
  }
}


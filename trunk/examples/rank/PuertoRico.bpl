//#rTerminationDerivable
/*
 * Date: 2012-07-06
 * Author: leike@informatik.uni-freiburg.de
 *
 * Ranking function: f(x) = 0.
 * Loop iteration is impossible.
 */

procedure PuertoRico(c: int) returns (x: int)
free requires c > 0;
{
  while (c <= 0) {
    x := x + c;
  }
}

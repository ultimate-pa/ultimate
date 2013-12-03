//#rTermination
/*
 * Date: 2013-01-15
 * Author: leike@informatik.uni-freiburg.de
 *
 * Ranking function: f(y) = y
 * with supporting invariant x8 >= x0 + 1.
 *
 * Nevertheless, a more precise supporting invariant
 * x8 >= x0 + 99999999 is discovered.
 */

procedure ExponentialGrowth() returns (y: int, z: int)
{
  var x0, x1, x2, x3, x4, x5, x6, x7, x8: int;
  x0 := 1;
  x1 := 10*x0;
  x2 := 10*x1;
  x3 := 10*x2;
  x4 := 10*x3;
  x5 := 10*x4;
  x6 := 10*x5;
  x7 := 10*x6;
  x8 := 10*x7;
  while (y >= 0) {
    y := y - x8 + x0;
  }
}

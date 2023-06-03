//#rTerminationDerivable
/*
 * Date: 2014-06-05
 * Author: leike@informatik.uni-freiburg.de
 *
 * The variables z and y is rotated by 180 degrees in each loop execution.
 *
 * This program has the following multiphase ranking function:
 * f_0(x, y) = 2q + z - y + 2
 * f_1(x, y) = q + 1
 *
 * This is Example 4.16 in my Master's Thesis.
 * It is simplified as Example 7 in our TACAS'2014 paper,
 * and we claim that it does not have a multiphase ranking function.
 * But it does!
 *
 * Thanks to Samir Genaim for pointing this out.
 */

procedure main() returns ()
{
  var q, z, y: real;
  assume(z >= y + 1.0);
  while (q >= 0.0) {
    q := q + z - y - 1.0;
    y := 0.0 - y;
    z := 0.0 - z;
  }
}

//#rTerminationDerivable
/*
 * Date: 2014-06-05
 * Author: leike@informatik.uni-freiburg.de
 *
 * The variable z is rotated by 180 degrees in each loop execution.
 *
 * This program has the following multiphase ranking function:
 * f_0(x, y) = 2q + z
 * f_1(x, y) = q
 *
 * This is listed as Example 7 in our TACAS'2014 paper as not having
 * a multiphase ranking function. But it does!
 *
 * Thanks to Samir Genaim for pointing this out.
 */

procedure main() returns ()
{
  var q, z: real;
  while (q > 0.0) {
    q := q + z - 1.0;
    z := 0.0 - z;
  }
}

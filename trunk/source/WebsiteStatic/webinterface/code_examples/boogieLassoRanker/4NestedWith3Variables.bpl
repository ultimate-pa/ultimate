//#rTerminationDerivable
/*
 * Date: 2014-06-08
 * Author: leike@informatik.uni-freiburg.de
 *
 * (a, b) is a vector that is rotated around (0, 0) and scaled by a factor of 5.
 * I.e., (a, b) is on an outward spiral around (0, 0).
 *
 * This program terminates because on average, (a, b) is (0, 0),
 * hence q decreases by 1 on average.
 *
 * This example has 3 variables and a 4-nested ranking function:
 * f0 = 10*q - a - 2*b
 * f1 =  2*q + a - 2*b
 * f2 = a
 * f3 = q
 *
 * It does not have a 3-nested ranking function.
 *
 * See also MultiphaseRotation53.bpl
 * and CrazySpirals.bpl.
 */

procedure main() returns ()
{
  var q, a, b: real;
  while (q > 0.0) {
    q    := q + a - 1.0;
    a, b := 3.0*a - 4.0*b, 4.0*a + 3.0*b;
  }
}

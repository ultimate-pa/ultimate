//#rTerminationDerivable
/*
 * Date: 2014-06-05
 * Author: leike@informatik.uni-freiburg.de
 *
 * The vector (a, b) is rotated by an irrational angle of
 * arccos(0.6) ~ 53.13 degrees in each loop execution.
 *
 * Ultimate returns the following 3-phase ranking function:
 * f_0(x, y) = 10*q + 13*a - 10*b + 10
 * f_1(x, y) = 36*q + 25*a + 20
 * f_2(x, y) = q + 1
 * This ranking function appears to be invalid.
 *
 * This is a generalization of Example 7 in our TACAS'2014 paper.
 */

procedure main() returns ()
{
  var q, a, b: real;
  while (q > 0.0) {
    q := q + a - 1.0;
    a := 0.6*a - 0.8*b;
    b := 0.8*a + 0.6*b;
  }
}

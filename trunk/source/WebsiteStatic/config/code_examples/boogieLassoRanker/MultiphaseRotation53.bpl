//#rTerminationDerivable
/*
 * Date: 2014-06-05
 * Author: leike@informatik.uni-freiburg.de
 *
 * The vector (a, b) is rotated by an irrational angle of
 * arccos(0.6) ~ 53.13 degrees in each loop execution.
 *
 * Has the following 3-nested ranking function:
 * f0 = 2*q + a - 2*b
 * f1 = 4*q + 5*a
 * f2 = 5*q
 *
 * This is a generalization of Example 7 in our TACAS'2014 paper.
 */

procedure main() returns ()
{
  var q, a, b: real;
  while (q > 0.0) {
    q    := q + a - 1.0;
    a, b := 0.6*a - 0.8*b, 0.8*a + 0.6*b;
  }
}

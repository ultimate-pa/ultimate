//#rTerminationDerivable
/*
 * Date: 2014-06-05
 * Author: leike@informatik.uni-freiburg.de
 *
 * The vector (a, b) is rotated by an irrational angle of
 * arccos(0.6) ~ 53.13 degrees in each loop execution.
 *
 * This has the following 3-nested ranking function:
 * f0 = 2*q + a - 2*b
 * f1 = 4*q + 5*a
 * f2 = 5*q
 *
 * This is a nondeterministic version of MultiphaseRotation53.bpl.
 */

procedure main() returns ()
{
  var q, a, b, old_a, old_b, old_q: real;
  while (q > 0.0) {
    old_q := q;
    old_a := a;
    old_b := b;
    havoc q;
    havoc a;
    havoc b;
    assume(q <= old_q + old_a - 1.0);
    assume(a <= 0.6*old_a - 0.8*old_b);
    assume(b >= 0.8*old_a + 0.6*old_b);
  }
}

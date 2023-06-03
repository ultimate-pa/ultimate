//#rTerminationDerivable
/*
 * Date: 2014-06-29
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(x) = x
 *
 * This is the Waldkirch example with the additional not-equal relations
 *     x != a, x != b, x != c, x != d,
 * which are not relevant for a termination proof.
 * These not-equal relations slow down the synthesis significantly because we
 * have to translate each of them into a disjunction of two inequalities.
 */

procedure main() returns ()
{
  var x, a, b, c, d : int;
  while (x >= 0) {
    x := x - 1;
    assume (x != a);
    assume (x != b);
    assume (x != c);
//    assume (x != d);
  }
}


//#Safe
/*
 * Revealed problem in invariant synthesis with support of WP
 * overapproximations.
 * WP was negated over integers.
 * I think we have to negate it over reals.
 * 
 * Date: 2017-02-12
 * Author: heizmann@informatik.uni-freiburg.de and Betim Musa
 *
 */

var x, y: int;

procedure main()
{
  assume x < y;

  while (*) { }

  assert(x < 100 || y >= 100);
}

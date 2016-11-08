//#Unsafe
/*
 * Date: 2014-09-07
 * Author: heizmann@informatik.uni-freiburg.de
 * Revealed bug in CNF conversion.
 * We use the "useless" while loop to avoid that the large block encoding
 * reduces the program into a single method.
 *
 */

var A, B, C, D, E : bool;

procedure method1() returns ()
{
  if (*) {
    assume(false);
  } else {
     assume(!( (A || B) && B));
  }
  while (*) {
      assume(true);
    }
  assert(false);
}



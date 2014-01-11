//#Safe
/*
 * Date: 02.11.2013
 * Author: heizmann@informatik.uni-freiburg.de
 * Revealed bug in CNF conversion for implication.
 * We use the "useless" while loop to avoid that the large block encoding
 * reduces the program into a single method.
 *
 */

var x,y,a,b : int;

procedure method1() returns ()
modifies x,y,a,b;
{
  assume(true);
  assume(a != b ==> false);
  while (*) {
      assume(true);
    }
  assert(a == b);
}



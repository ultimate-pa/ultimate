//#Safe
/*
 * Date: 2015-02-24
 * Author: heizmann@informatik.uni-freiburg.de
 * Test for the "resolution like" optimization in XNF convertion
 *
 */

var A, B, C, D, E : bool;

procedure proc() returns ()
{
  if (*) {
    assume(false);
  } else {
     assume((!A && B) || (!B && C && D) || (A && E) || A || (D && E) || (C && D));
  }
  while (*) {
      assume(true);
    }
  assert(A || B || D);
}



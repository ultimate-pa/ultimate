//#rTerminationDerivable
/*
 * Date: 21.09.2013
 * Author: leike@informatik.uni-freiburg.de
 *
 * This is a modified version of the program "SIMPLE" from Fig.1 of
 * A. R. Bradley, Z. Manna, and H. B. Sipma.
 * The polyranking principle.
 * In ICALP, pages 1349–1361. Springer, 2005.
 * 
 * In this modified version we replaced nondeterministic updates by 
 * deterministic updates.
 * 
 * This program has a 2-phase ranking function.
 */

procedure main() returns ()
{
  var x,y,N: int;
  assume(x + y >= 0);
  while (x <= N) {
    if (*) {
      x := 2*x + y;
      y := y + 1;
    } else {
      x := x + 1;
    }
  }
}


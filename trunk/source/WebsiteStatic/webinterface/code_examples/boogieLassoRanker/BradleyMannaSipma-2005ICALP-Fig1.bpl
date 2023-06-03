//#rTerminationDerivable
/*
 * Date: 21.09.2013
 * Author: leike@informatik.uni-freiburg.de
 *
 * Updated: 2014-10-17
 * (fixed a small error)
 *
 * This is the program "SIMPLE" from Fig.1 of
 * A. R. Bradley, Z. Manna, and H. B. Sipma.
 * The polyranking principle.
 * In ICALP, pages 1349–1361. Springer, 2005.
 *
 * This program has a 2-phase ranking function.
 */

procedure main() returns ()
{
  var x,x_old,y,y_old: int;
  var N: int;
  assume(x + y >= 0);
  while (x <= N) {
    x_old := x;
    y_old := y;
    havoc x,y;

    if (*) {
      assume(x >= 2*x_old + y_old);
      assume(y >= y_old + 1);
    } else {
      assume(x >= x_old + 1);
      assume(y == y_old);
    }
    
    havoc x_old;
    havoc y_old;
  }
}


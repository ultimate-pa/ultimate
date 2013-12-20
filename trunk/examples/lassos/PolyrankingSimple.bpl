//#rTerminationDerivable
/*
 * Boogie implementation of program SIMPLE (Fig.1) from the following paper.
 * 2005ICALP -Bradley,Manna,Sipma - The Polyranking Principle
 *
 * Date: 25.04.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(x, y) = 2x + y.
 */

var x,y,N: int;
var xOld,yOld: int;
procedure main() returns ()
modifies x,y,xOld,yOld;
{
  assume (x+y>=0);
  while (x<=N) {
    xOld := x;
    yOld := y;
    if(*) {
      havoc x,y;
      assume(x >= xOld + yOld);
      assume(y >= yOld + 1);
    } else {
      assume(x >= xOld + 1);
    }
  }
}


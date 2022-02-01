//#rNonTermination
/*
 * Date: 2014-07-01
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var a,b,c,d : [int] int;
var i,j,k : int;

procedure main() returns ()
modifies b;
{
  while (true) {
    assume a == b;
    b[3] := c[3] + 1;
    assume d[3] >= 0;
    assume d == b;
  }
}


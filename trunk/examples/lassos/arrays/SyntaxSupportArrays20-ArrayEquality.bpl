//#rTermination
/*
 * Date: 2014-07-04
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var a,b,c,d : [int] int;
var i,j,k : int;

procedure main() returns ()
modifies b;
{
  while (true) {
    assume a == c;
    b[3] := b[3] - a[2];
    assume d[3] >= 0;
    assume d == b;
    assume c[2] > 1;
  }
}


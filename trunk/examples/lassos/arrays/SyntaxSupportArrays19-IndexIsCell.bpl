//#rUnknownTermination
/*
 * Date: 2014-07-01
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var a : [int] int;
var i,j,k : int;

procedure main() returns ()
modifies a;
{
//  assume i != j;
  while (a[a[i]] >= 0) {
    a[a[i]] := a[a[i]] - 1;
//    a[k] := a[k] + 1;
  }
}


//#rNonTermination
/*
 * We fail to prove anything because the resulting formula seems to be too
 * large for DNF convertion.
 * Date: 2014-06-23
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var a : [int] int;
var i,j,k : int;

procedure main() returns ()
modifies a;
{
  while (true) {
    a[j] := a[j] + 1;
    a[i] := a[i] - 1;
    a[k] := a[k] - 1;
  }
}


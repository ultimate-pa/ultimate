//#rTermination
/*
 * Date: 2015-05-24
 * Author: heizmann@informatik.uni-freiburg.de
 * Shows that in r14358 RewriteArrays is very inefficient because it
 * does also a case distinction for the invars of x,y,z although these do
 * not occur in the formula.
 */
var a : [int] int;
var k, x, y, z : int;


procedure main() returns ()
modifies a, k, x, y, z;
{
  while (a[k] > 0) {
    a[k] := a[k] - 1;
    assume k > 7;
    x := 1;
    y := 2;
    z := 3;
    a[x] := 1;
    a[y] := 2;
    a[z] := 3;
  }
}


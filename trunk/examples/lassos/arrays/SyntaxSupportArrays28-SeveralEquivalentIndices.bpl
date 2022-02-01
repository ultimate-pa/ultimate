//#rTermination
/*
 * Date: 2016-09-16
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var a : [int] int;
var i,j,k,l,m,n : int;
var x : int;

procedure main() returns ()
modifies a, x;
{
  assume a[i] == 1;
  assume i == j && j == k && k == l && l == m && m == n;
  a[42] := 2;
  while (x >= 0) {
    x := x + 5;
    x := x - a[i];
    x := x - a[j];
    x := x - a[k];
    x := x - a[l];
    x := x - a[m];
    x := x - a[n];
  }
}


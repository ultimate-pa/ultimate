//#rTerminationDerivable
/*
 * Date: 2012-06-10
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Since a[0] != a[k], k cannot be 0
 *
 *
 */
var a : [int] int;
var b : [int] int;
var x, k : int;

procedure main() returns ()
modifies a, x, k;
{
  assume k >= 0;
  assume a[0] == 23;
  assume a[k] == 42;
  while (x >= 0) {
    x := x - k;
  }
}


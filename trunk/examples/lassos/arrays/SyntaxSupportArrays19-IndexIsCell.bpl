//#rTerminationDerivable
/*
 * Date: 2014-07-01
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var a : [int] int;

procedure main() returns ()
modifies a;
{
  a[a[7]] := 23;
  while (a[a[7]] >= 0) {
    a[a[7]] := a[a[7]] - 1;
  }
}



//#Safe
/* Date: 2014-07-06
 * Author: heizmann@informatik.uni-freiburg.de
 */
var a : [int] int;
var upper : int;
var i : int;

procedure main() returns();
modifies a, i, upper;

implementation main() returns()
{
  assume upper >= 0;
  a[upper] := 23;
  i := 0;
  while(a[i] != 23) {
    assert(i < upper);
    i := i + 1;
  }
}


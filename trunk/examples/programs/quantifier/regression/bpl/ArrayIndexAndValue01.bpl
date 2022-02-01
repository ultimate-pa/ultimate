//#Safe
/* Date: 2014-07-06
 * Author: heizmann@informatik.uni-freiburg.de
 */
var a : [int] int;
var upper : int;

procedure ULTIMATE.start() returns();
modifies a, upper;

implementation ULTIMATE.start() returns()
{
  var i : int;
  assume upper >= 0;
  a[upper] := 23;
  assume i <= upper;
  call proc(i);
}

procedure proc(iin : int) returns()
modifies a;
{
  var i : int;
  i := iin;
  while(a[i] != 23) {
    assert(i < upper);
    i := i + 1;
  }
}
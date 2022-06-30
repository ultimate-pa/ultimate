//#Unsafe

/*
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 30.06.2022
 */

var x: int;

procedure thread1() returns()
modifies x;
{
  x := 1;
}

procedure ULTIMATE.start() returns()
modifies x;
{
  var i : int;
  var j : int;
  x := 0;
  i := x;
  assert x == 0;
  // Error Location == 0
  fork 1 thread1();
  j := x - 2;
  assert x == 1;
}

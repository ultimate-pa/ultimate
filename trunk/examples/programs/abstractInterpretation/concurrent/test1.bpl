//#Unsafe

/*
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 30.06.2022
 */

var x: int;

procedure thread1() returns()
modifies x;
{
  x := 2;
}

procedure ULTIMATE.start() returns()
modifies x;
{
  var i : int;
  var j : int;
  x := 0;
  fork 1 thread1();
  x := x + 1;
  assert x == 1;
  i := x + 1;
  x := i + 1;
  assert x == 1;
  assert 0 <= x && x <= 1;
  x := x + i;
}

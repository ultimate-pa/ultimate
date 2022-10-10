//#Unsafe

/*
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 20.09.2022
 */

var x : int;
var y : int;


procedure thread1() returns ()
modifies x, y;
{
  while (x <= 0) {
    x := x + 1;
  }
}

procedure thread2() returns ()
modifies x, y;
{
  while (y <= 0) {
    y := y + 1;
  }
}

procedure ULTIMATE.start() returns ()
modifies x, y;
{
  assume x == y && x == -1;
  fork 1 thread1();
  fork 2 thread2();
  join 1;
  join 2;
  assert x == y && x <= 0;
}


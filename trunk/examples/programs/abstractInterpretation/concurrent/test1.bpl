//#Unsafe

/*
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 30.06.2022
 */

var x,y: int;

procedure thread1() returns()
modifies x,y;
{
  x := x-y;
  y := x;
}

procedure ULTIMATE.start() returns()
modifies x,y;
{
  var i : int;
  i := -2;
  x := 0;
  y := x - i;
  fork 1 thread1();
  while (i < 0) {
     i := i + 1;
     y := x + y;
     x := y;
  }
  assert y >= 2;
  x := y + i;
}

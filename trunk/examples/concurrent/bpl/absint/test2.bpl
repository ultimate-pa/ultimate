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

procedure thread2() returns()
modifies x;
{
  x := 2;
}

procedure thread3() returns()
modifies x;
{
  x := 11;
}

procedure ULTIMATE.start() returns()
modifies x;
{
  var i : int;
  x := 0;
  i := x;
  fork 1 thread1();
  fork 2 thread2();
  while(x < 10) {
    x := x + 1;
  }
  fork 3 thread3();
  assert x <= 10;
}

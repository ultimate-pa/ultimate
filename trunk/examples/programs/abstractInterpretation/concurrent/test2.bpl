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
  assert x <= 6; // ERROR
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
  assert x == 0;
  fork 1 thread1();
  assert x <=1 && x >= 0;
  fork 2 thread2();
  assert x <=2 && x >= 0;
  while(x < 10) {
    x := x + 1;
  }
  fork 3 thread3();
  assert x <= 10; // ERROR
}

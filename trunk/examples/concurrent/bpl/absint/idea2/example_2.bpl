//#Safe

/*
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 206.09.2022
 */

var x0: int;
var x1: int;

procedure thread1() returns()
modifies x0, x1;
{
  x0 := x1 + 1;
}

procedure thread2() returns()
modifies x0, x1;
{
  x1 := x0 - 1;
}

procedure ULTIMATE.start() returns()
modifies x0, x1;
{
  
  x0 := 0;
  x1 := 0;

  while (*) {
    fork 1 thread1();
    fork 2 thread2();
  }

  assert x0 >= x1;
}

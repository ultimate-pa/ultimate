//#Safe

/*
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 206.09.2022
 */

var x0: int;
var x1: int;

procedure thread1() returns()
modifies x1;
{
  x1 := x1 + 1;
}

procedure ULTIMATE.start() returns()
modifies x0, x1;
{
  
  x0 := 0;
  x1 := 0;

  while (*) {
    fork 1 thread1();
  }

  assert x0 == 0;
}

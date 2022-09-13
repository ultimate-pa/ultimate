//#Safe

/*
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 206.09.2022
 */

var x0: int;
var x1: int;
var x2: int;

procedure thread1() returns()
modifies x0, x1, x2;
{
  var t1 : int;
  var t2 : int;
  t1 := x1;
  x1 := x0;
  t2 := x2;
  x2 := t1;
  x0 := t2;
  assert x0 == 0 && x1 == 0 && x2 == 0;
}

procedure ULTIMATE.start() returns()
modifies x0, x1, x2;
{
  
  x0 := 0;
  x1 := 0;
  x2 := 0;

  while (*) {
    fork 1 thread1();
  }
}

// Safe

/*
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 28.07.2022
 */

var x : int;
var y : int;
procedure ULTIMATE.start() returns()
modifies x, y;
{
  x := 0;
  y := 0;
  fork 1 thread1();
  fork 2 thread2();
}


procedure thread1() returns()
modifies x, y;
{
  x := 1;
  y := 1;
}


procedure thread2() returns()
modifies x, y;
{
  var a : int;
  var b : int;
  a := x;
  b := y;
  
  // data dependent
  // a := b;
  
  // control-dependent
  // if (a > 0) {
  //   b := 2;
  // }
  
  assert a >= 0;
  assert b >= 0;
}

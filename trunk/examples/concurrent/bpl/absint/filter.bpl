//#Safe

/*
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 28.07.2022
 */

var flag : bool;
var x : int;
procedure ULTIMATE.start() returns()
modifies flag, x;
{
  flag := false;
  x := 0;
  fork 1 thread1();
  fork 2 thread2();
}


procedure thread1() returns()
modifies flag, x;
{
  x := 4;
  x := 5;
  flag := true;
}


procedure thread2() returns()
modifies flag, x;
{
  var b : bool;
  var t : int;
  b := flag;
  if (b) {
    t := x;
    assert t == 5;
  }
}
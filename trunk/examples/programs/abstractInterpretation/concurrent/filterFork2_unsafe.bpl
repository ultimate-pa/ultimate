//#Unsafe

/*
 * Version 3 is unsound for this program
 *
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 28.07.2022
 */

var x : int;
var m : int;
procedure ULTIMATE.start() returns()
modifies m, x;
{
  m := 0;
  fork 1 thread1();
  fork 2 thread2();
}


procedure thread1() returns()
modifies m, x;
{
  atomic{ assume m == 0; m := 1;}
  x := 1;
  assert x == 1;
  m := 0;
}

procedure thread2() returns()
modifies m, x;
{
  atomic {assume m == 0; m := 1;}
  x := 0;
  m := 0;
}

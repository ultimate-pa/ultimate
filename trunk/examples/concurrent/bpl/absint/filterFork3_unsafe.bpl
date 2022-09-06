//#Unsafe

/*
 * Version 3 is unsound for this program
 *
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 28.07.2022
 */

var x : int;
procedure ULTIMATE.start() returns()
modifies x;
{
  x := 1;
  fork 1 thread1();
  x := 0;
  x := 0 + 1; // just to differentiate between the two x := 1 statements
  fork 2 thread1();
}


procedure thread1() returns()
modifies x;
{
  var i : int;
  i := x;
  assert i == 1;
}

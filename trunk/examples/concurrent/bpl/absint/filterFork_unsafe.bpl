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
  x := 0;
  while(*) {
    fork 1 thread1();
  }
}


procedure thread1() returns()
modifies x;
{
  x := 1;
  x := 2;
  assert x == 2;
}

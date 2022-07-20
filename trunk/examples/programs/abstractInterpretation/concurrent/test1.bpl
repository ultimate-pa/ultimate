//#Unsafe

/*
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 30.06.2022
 */

var x,y: int;

procedure thread1() returns()
modifies x,y;
{
  // x: 0; y: 2
  y := x;
  x := x-y;
}

procedure ULTIMATE.start() returns()
modifies x,y;
{
  var i : int;
  i := -2;
  x := 0;
  // x 0
  y := x - i;
  // y = -2
  fork 1 thread1();
  while (i < 0) {
     i := i + 1;
     y := x + y;
  }
  x := x + 1; 
  // fork 2 thread1();
  x := y + i;
}

//#Unsafe

/*
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 07.06.2022
 */

var x: int;
var y: int;

procedure thread1() returns()
modifies x,y;
{
   x := x + 1;
   fork 3 thread3();
}

procedure thread2() returns()
modifies x;
{
   x := x-1;
}

procedure thread3() returns()
modifies y;
{
  y := 0;
}

procedure ULTIMATE.start() returns()
modifies x,y;
{
   x := 1;
   fork 1 thread1();
   while (x > 0) {
      fork 2 thread2();
   }
   y := x;
   assert y == 0;
}

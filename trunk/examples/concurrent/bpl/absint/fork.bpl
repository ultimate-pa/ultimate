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
  var i : int;
  i := 2;
  y := 3;
  x := 2 * y; // ultimate, thread2 +
  fork 3 thread3();
  while (i < 5) {
     i := i + 1;
     x := i;
  }
  x := x-y; // ultimate, thread2, thread3 +
}

procedure thread2() returns()
modifies x,y;
{
 var i : int;
 x := 3;
 if (i < 5) {
     i := i + 1;
     y := x; // ultimate, thread2, thread1, thread3 +
 } else {
     x := i;
     i := i - 1;
 }
 i := i/x; //ultimate, thread1, thread2, thread3 +
}

procedure thread3() returns()
modifies y;
{
  y := 0;
}

procedure ULTIMATE.start() returns()
modifies x,y;
{
 var j : int;
 y := 2;
 x := y; // +
 fork 1 thread1();
 j := y; // thread1, thread3 +
 
 while (j > 1) {
     x := y; // thread1, thread2, thread3 +
     j := j - 1;
     fork 2 thread2();
 }
}

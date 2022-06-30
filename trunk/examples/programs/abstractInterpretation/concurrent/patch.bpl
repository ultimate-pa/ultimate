//#Unsafe

/*
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 30.06.2022
 */

var x: int;

procedure thread1() returns()
modifies x;
{
  var l : int;
  l := 0;
  x := 1; // 1
  x := x-3; // -2
}

procedure thread2() returns()
modifies x;
{
  var l : int;
  l := 0;
  x := 0; // 0
  x := x-2; // [-u,3] && [-2, u]
  while(l < 3) {
    l := l + 1;
    x := l; // [-u,3] && [-2, u]
  }
}

procedure ULTIMATE.start() returns()
modifies x;
{
  var i : int;
  x := 2; // 2
  fork 1 thread1();
  fork 2 thread2();
  i := x;  
}

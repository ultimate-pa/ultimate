// Safe

/*
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 28.07.2022
 */

var flag : bool;
var x : int;
var y : int;
procedure ULTIMATE.start() returns()
modifies flag, x, y;
{
  flag := false;
  x := 0;
  if (flag) {
     fork 1 thread1();
  }
  fork 2 thread2();
}


procedure thread1() returns()
modifies y;
{
  y := 4;
}


procedure thread2() returns()
modifies flag, x;
{
  var b : bool;
  b := flag;
  if (b) {
    x := 0;
    while(flag) {
      havoc flag;
    }
    x := x + 1;
  } else {
    b := true;
  }
  
  if (x == 1) {
    x := 0;
  }
  
  assert x == 0;
}

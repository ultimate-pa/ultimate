//#Unsafe

/*
 * Author: Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Date: 30.06.2022
 */

var x: int;

procedure thread1() returns()
modifies x;
{
  x := 10;
  assert x == 10; // ERROR
}

procedure thread2() returns()
modifies x;
{
  x := 1;
}

procedure ULTIMATE.start() returns()
modifies x;
{
  var i : int;
  x := 0;
  i := x + 1;
  fork 2 thread2();
  if(x>0) {
    x := 3;
  } 
  fork 1 thread1();
  assert 0 <= x && x <= 10;
  while(i<3) {
    i := i + 1;
    x := x + 1;
    fork 1 thread1();
  }
  assert x <= 11; // ERROR
}

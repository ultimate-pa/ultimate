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
  assert x == 10;
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
    x := 0;
  } 
  fork 1 thread1();
  assert x == 0; // ERROR
  while(i<3) {
    i := i + 1;
    x := x + 1;
    fork 1 thread1();
  }
  assert x <= 11; // should be correct, not able to prove
}

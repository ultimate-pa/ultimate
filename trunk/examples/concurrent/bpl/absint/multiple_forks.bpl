//#Unsafe
/*
 * Date: 2022-10-13
 * schuessf@informatik.uni-freiburg.de
 *
 */

var x: int;

procedure ULTIMATE.start()
modifies x;
{
  var i : int;
  
  fork 1 thread1();
  i := 0;
  fork 2 thread2();
  x := i;
  assert x == 0;
}

procedure thread1()
modifies x;
{
  x := x + 1;
  fork 3 thread2();
}

procedure thread2()
modifies x;
{
  x := 0;
}
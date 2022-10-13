//#Safe
/*
 * Date: 2022-10-13
 * schuessf@informatik.uni-freiburg.de
 *
 */

var x, y: int;

procedure ULTIMATE.start()
modifies x, y;
{
  x := y + 1;
  fork 0 thread();
  assert x > y;
}

procedure thread()
modifies x, y;
{
  atomic { havoc x, y; assume x > y; }
  x := x + 1;
  y := y + 1;
}
//#Unsafe
/*
 * Date: 2022-10-13
 * schuessf@informatik.uni-freiburg.de
 *
 */

var x, y: int;

procedure ULTIMATE.start()
modifies x, y;
{
  assume x == y;
  fork 0 thread();
  assert x == y;
}

procedure thread()
modifies x, y;
{
  x := 0;
  y := 0;
}
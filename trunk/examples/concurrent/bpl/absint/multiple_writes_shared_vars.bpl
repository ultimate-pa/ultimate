//#Safe
/*
 * Date: 2022-10-13
 * schuessf@informatik.uni-freiburg.de
 *
 */

var x, y, z: int;

procedure ULTIMATE.start()
modifies x, y, z;
{
  assume x == y;
  fork 0 thread();
  assert x == y || z == 1;
}

procedure thread()
modifies x, y, z;
{
  atomic { x := 0; y := 0; }
  atomic { y := 1; z := 1; }
}
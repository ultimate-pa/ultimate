//#Safe
/*
 * author: nutz@informatik.uni-freiburg.de
 */

procedure SAS09paper()
{
  var x, y, z, a: int;

  x := 0;
  y := 0;
  z := 0;
  a := 0;

  while (*) {
    x := x + 1;
  }

  while (*) {
    y := y + 1;
  }

  while (*) {
    z := z + 1;
  }

  while (*) {
    a := a + 1;
  }

  assert(x != -1 && y != -1 && z != -1 && a != -1);
}


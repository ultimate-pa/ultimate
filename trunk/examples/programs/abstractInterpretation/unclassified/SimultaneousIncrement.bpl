//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 7.8.2010
 * Example related to SimultaneousDecrement which is also correct wrt.
 * to the assertion.
 */
procedure SimultaneousIncrement()
{
  var x, y, i, j, d: int;

  x := 0;
  i := 0;
  d := y - j;

  while (*) {
    x := x+1;
    y := y+1;
  }
  while (*) {
    i := i+1;
    j := j+1;
  }
  if (j==y) {
    assert(x==i-d);
  }
}


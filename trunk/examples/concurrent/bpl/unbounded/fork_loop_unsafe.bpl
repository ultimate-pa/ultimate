//#Unsafe

/*
 * Example that is unsafe, but only with >=3 threads
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2020-10-21
 *
 */

var x: int;

procedure thread(y: int) returns()
modifies x;
{
  x := x + 1;
  assert x <= y + 2;
}

procedure ULTIMATE.start() returns()
modifies x;
{
  var i : int;
  x := 0;
  i := 0;

  while (*) {
    fork i thread(i);
	i := i + 1;
  }
}

//#Safe
/*
 * Date: 2018-10-17
 * schuessf@informatik.uni-freiburg.de
 *
 */

var a, b, c : [int] int;
var i : int;

procedure main() returns ()
modifies a, i;
{
  assume i > 0;
  assume b == c;
  while (i > 0) {
    a := b;
    i := i - 1;
  }
  assert a == c;
}
//#Safe
/*
 * Date: 2018-10-09
 * schuessf@informatik.uni-freiburg.de
 *
 */

var a, b, c : [int] int;
var i : int;

procedure main() returns ()
modifies a;
{
  assume b == c;
  a := b;
  assert a == c;
}
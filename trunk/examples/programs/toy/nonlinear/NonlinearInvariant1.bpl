//#Safe
/*
 * Date: 2015-01-24
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var a,b: int;

procedure main() returns ()
modifies a,b;
{
  assume a * b > 0;
  while (*) {
    if (a >= 0)  {
        a := a + 1;
    } else {
        a := a - 1;
    }
    if (b >= 0)  {
        b := b + 1;
    } else {
        b := b - 1;
    }
  }
  assert a * b > 0;
  
}

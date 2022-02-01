//#rTermination
/*
 * Date: 2014-03-05
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

var x:int;

procedure main() returns ()
modifies x;
{
  while (x % 2 == 0) {
    x := x - 1;
  }
}

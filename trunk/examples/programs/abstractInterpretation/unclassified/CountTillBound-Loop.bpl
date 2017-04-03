//#Safe
/*
 * Ultimate Automizer ist not are unable to prove safety (efficiently) because
 * (in r9676) we get the following interpolants.
 * [(<= _x_-1 0), (<= _x_1 1), (<= _x_2 2), false]
 * 
 * Date: 23.09.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

var x:int;

procedure main()
modifies x;
{
  x := 0;
  while (x < 100) {
    x := x + 1;
  }

  assert(x == 100);
}
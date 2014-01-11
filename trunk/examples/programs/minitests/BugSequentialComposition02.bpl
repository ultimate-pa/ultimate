//#Unsafe
/*
 * Bug in sequential composition in r6168
 * Date: 06.06.2011
 * Author: heizmann@informatik.uni-freiburg.de
 */

procedure proc()
{
  var in, a, y: int;

  y, a := 0, 10;
  a := y;
  a := y;
  assert (y == 1);

}

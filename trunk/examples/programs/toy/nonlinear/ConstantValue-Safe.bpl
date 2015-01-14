//#Safe
/*
 * Date: 2015-01-14
 * Author: heizmann@informatik.uni-freiburg.de
 *
 *
 */


procedure main()
{
  var x, y: int;

  assume (x >= 0);
  assume (y >= 0);

  while (*)
  {
    x := x * y;
  }
  assert (x >= 0);
}

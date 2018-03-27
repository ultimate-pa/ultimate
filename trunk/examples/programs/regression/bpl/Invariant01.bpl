//#Unsafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2018-03-27
 * 
 */
procedure main()
{
  var x: int;

  x := 5;

  while (x >= 0)
    invariant x >= 3;
  {
    x := x - 1;
  }
}


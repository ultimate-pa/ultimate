//#Unsafe
/*
 * Author: Miriam Herzig, Matthias Heizmann
 * Date: 2021-03-24
 * 
 */
var x, y : int;

procedure main() returns ()
modifies x;
{
  assume x < 0;
  while(x < 100)
  {
      x := x + 10;
  }
  assert x != 110;
}



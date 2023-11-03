//#Unsafe
/*
 * Author: Matthias Heizmann
 * Date: 2022-09-18
 * 
 */

var x, y : int;


procedure main() returns () 
modifies x,y;

{
  x := 5;
  y := 0;
  while(*)
  {
      x := -x + y;
      y := y + 1;
  }
  assert x != -3 && x != 5;
}

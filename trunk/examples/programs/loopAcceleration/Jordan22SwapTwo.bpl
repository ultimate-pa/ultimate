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
  y := 4;
  while(*)
  {
      x,y := y,x;
  }
  assert x == 5;
}

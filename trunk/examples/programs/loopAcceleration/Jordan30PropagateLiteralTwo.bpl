//#Safe
/*
 * Author: Matthias Heizmann
 * Date: 2022-09-21
 * 
 */

var x, y, a : int;


procedure main() returns () 
modifies x,y;

{
  x := 5;
  y := 4;
  while(x + a >= 42)
  {
      x := y;
      y := 23;
  }
  assert x == 5 || x == 4 || x == 23;
}

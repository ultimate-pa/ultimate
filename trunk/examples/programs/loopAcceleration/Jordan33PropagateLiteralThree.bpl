//#Unsfe
/*
 * Author: Matthias Heizmann
 * Date: 2022-12-11
 * 
 */

var x, y, z, a : int;


procedure main() returns () 
modifies x,y,z;

{
  x := 5;
  y := 4;
  z := 3;
  while(x + a >= 42)
  {
      x := y;
      y := z;
      z := 23;
  }
  assert x == 5 || x == 4 || x == 23;
}

//#Unsafe
/*
 * Author: Matthias Heizmann
 * Date: 2022-09-21
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
  }
  assert x == 5 || x == 3;
}

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
  while(x + a >= 42)
  {
      x := y;
      havoc y;
  }
  assert x == 5 || x == 4;
}

//#Unsafe
/*
 * Author: Matthias Heizmann
 * Date: 2022-09-19
 * 
 */

var x, y, z : int;


procedure main() returns () 
modifies x,y,z;

{
  x := 0;
  y := 0;
  z := 0;
  while(*)
  {
      z := z + y;
      y := y + x;
//      x := x + 1;
  }
  assert z < 1000;
}

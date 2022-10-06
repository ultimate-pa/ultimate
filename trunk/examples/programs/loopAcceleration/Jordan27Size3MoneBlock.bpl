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
  x := 3;
  y := 4;
  z := 5;
  while(*)
  {
      z := -z + y;
      y := -y + x;
      x := -x;
  }
  assert z < 1000;
}

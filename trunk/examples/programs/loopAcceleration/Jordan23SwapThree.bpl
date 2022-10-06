//#Unsafe
/*
 * Author: Matthias Heizmann
 * Date: 2022-09-18
 * 
 */

var x, y, z : int;


procedure main() returns () 
modifies x,y,z;

{
  x := 5;
  y := 4;
  z := 3;
  while(*)
  {
      x,y,z := z,x,y;
  }
  assert x == 5 || x == 4;
}

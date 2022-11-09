//#Unsafe
/*
 * Author: Matthias Heizmann
 * Date: 2022-09-18
 * 
 */

var x, y, z, u : int;


procedure main() returns () 
modifies x,y,z,u;

{
  x := 5;
  y := 4;
  z := 3;
  u := 2;
  while(*)
  {
      x,y,z,u := u,x,y,z;
  }
  assert x == 5 || x == 4 || x == 3;
}

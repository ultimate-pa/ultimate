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
  while(*)
  {
      x,y := y,-x;
  }
  assert x == 5 || x == -4 || x == -5;
}

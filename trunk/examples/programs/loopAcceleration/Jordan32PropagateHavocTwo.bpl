//#Unsafe
/*
 * Author: Matthias Heizmann
 * Date: 2022-09-21
 * 
 */

var x, y, z : int;


procedure main() returns () 
modifies x,y,z;

{
  x := 5;
  y := 4;
  while(*)
  {
      x := y;
      havoc y;
  }
  assert x == 5 || x == 4;
}

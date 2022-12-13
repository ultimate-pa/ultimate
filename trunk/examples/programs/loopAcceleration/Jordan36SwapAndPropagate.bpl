//#Unsafe
/*
 * Author: Matthias Heizmann
 * Date: 2022-12-11
 * 
 */

var x, y, z, u, v, a, i : int;


procedure main() returns () 
modifies x,y,z,u,v,i;

{
  x := 9;
  y := 8;
  z := 7;
  u := 0;
  v := 100;
  i := 0;
  while(x + a >= 42)
  {
      u, v := v, u;
      x := y;
      y := z;
      i := i + 1;
  }
  assert x == 9 || x == 7;
}

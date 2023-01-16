//#Safe
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
  u := 6;
  v := 5;
  i := 0;
  while(x + a >= 42)
  {
      x := y;
      y := z;
      z := u;
      u := v;
      havoc v;
      i := i + 1;
  }
  assert i == 0 ==> x == 9;
  assert i == 1 ==> x == 8;
  assert i == 2 ==> x == 7;
  assert i == 3 ==> x == 6;
}

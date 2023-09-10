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
  u := 0;
  v := 100;
  i := 0;
  while(x + a >= 42)
  {
      u, v := v + 1, u + x;
      x := y;
      y := z;
      i := i + 1;
  }
  assert i == 0 ==> u == 0 && v == 100;
  assert i == 1 ==> u == 101 && v == 9;
  assert i == 2 ==> u == 10 && v == 109;
  assert i == 3 ==> u == 110 && v == 17;
  assert i == 4 ==> u == 18 && v == 117;
  assert i == 5 ==> u == 118 && v == 25;
}

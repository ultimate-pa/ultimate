//#Safe
/*
 * Author: Matthias Heizmann
 * Date: 2022-10-26
 * 
 */

var x, y : int;


procedure main() returns () 
modifies x,y;

{
  x := 42;
  y := 0;
  while(*)
  {
      x := -x;
      y := y + 1;
  }
  assert y % 2 == 0 ==> x == 42;
  assert y % 2 == 1 ==> x == -42;
}

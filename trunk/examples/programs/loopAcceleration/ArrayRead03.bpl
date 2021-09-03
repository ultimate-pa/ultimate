//#Safe
/*
 * Author: Matthias Heizmann
 * Date: 2021-04-22
 * 
 */

var a : [int] int;
var k, x, y : int;
var B : bool;

procedure main() returns ()
modifies x,y,B;
{

  y := 3;
  x := 7;
  while(B)
  {
      y := 5;
      x := a[k];
      havoc B;
  }
  assert (y == 3 && x == 7) || (y == 5 && x == a[k]);
}



//#Unsafe
/*
 * Author: Matthias Heizmann
 * Date: 2022-09-24
 * 
 */

var x, y : int;


procedure main() returns () 
modifies x,y;

{
  assume (x >= 0 && y >= 0);
  while(x >= 256 && y >= 256)
  {
      x := x - 255;
      y := y - 255;
  }
  assert (0 <= x && x <= 255) || (0 <= y && y <= 255);
}

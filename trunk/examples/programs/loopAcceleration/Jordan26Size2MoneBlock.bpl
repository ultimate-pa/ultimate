//#Unsafe
/*
 * Author: Matthias Heizmann
 * Date: 2022-09-19
 * 
 */

var x, y : int;


procedure main() returns () 
modifies x,y;

{
  x := 3;
  y := 4;
  while(*)
  {
      y := -y + x;
      x := -x;
  }
//  assert y == 4 || y == 10 || y == -7 || y == -13 || y == 16 || y == -19;
  assert y < 1000;
}


//even
// y := -(-y + x) + -x
// y := y -2x
// y := y - k * 2x
// x := x
//odd
// y := -y+x+k*2x
// y := -y+(k*2+1)x

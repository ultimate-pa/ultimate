//#Unsafe
/*
 * Author: Matthias Heizmann
 * Date: 2022-12-22
 * 
 */

procedure main() returns () {
  var x,y : int;
  x := 0;
  while(x == y)
  {
      x := x + 1;
      havoc y;
  }
  assert x == 9999;
}



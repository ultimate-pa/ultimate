//#Unsafe
/*
 * Author: Matthias Heizmann
 * Date: 2021-04-22
 * 
 */

procedure main() returns () {
  var x, y : int;
  x := 7;
  while(y == 23)
  {
      x := 1;
      havoc y;
  }
  assert x == 7;
}



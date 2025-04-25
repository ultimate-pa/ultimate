//#Unsafe
/*
 * Author: Matthias Heizmann
 * Date: 2022-12-14
 * 
 */

procedure main() returns () {
  var x, y : int;
  x := 7;
  while(y == 23)
  {
      havoc y;
      x := y;
      havoc y;
  }
  assert x == 7;
}



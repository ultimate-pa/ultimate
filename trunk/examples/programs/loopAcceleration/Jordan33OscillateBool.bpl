//#Unsafe
/*
 * Author: Matthias Heizmann
 * Date: 2022-12-08
 * 
 */

procedure main() returns () {
  var x : int;
  var b : bool;
  x := 0;
  b := true;
  while(*)
  {
      x := x + 1;
      b := !b;
  }
  assert x == 9999 ==> b;
}



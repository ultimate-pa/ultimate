//#Unsafe
/*
 * Author: Matthias Heizmann
 * Date: 2021-04-22
 * 
 */

procedure main() returns () {
  var x : int;
  var B : bool;
  x := 7;
  while(B)
  {
      x := 1;
      havoc B;
  }
  assert x == 7;
}



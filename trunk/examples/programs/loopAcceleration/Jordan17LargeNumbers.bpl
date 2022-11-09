//#Unsafe
/*
 * Author: Matthias Heizmann
 * Date: 2022-09-24
 * 
 */

var x : int;


procedure main() returns () 
modifies x;

{
  assume x >= 123456;
  while(*)
  {
      x := x - 1234567;
  }
  assert 0 <= x;
}

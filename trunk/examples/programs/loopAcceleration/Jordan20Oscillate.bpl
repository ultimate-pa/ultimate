//#Safe
/*
 * Author: Matthias Heizmann
 * Date: 2022-09-18
 * 
 */

var x : int;


procedure main() returns () 
modifies x;

{
  x := 5;
  while(*)
  {
      x := -x + 2;
  }
  assert x == -3 || x == 5;
}

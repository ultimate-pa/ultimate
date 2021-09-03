//#Safe
/*
 * Author: Matthias Heizmann
 * Date: 2021-04-11
 * 
 */

procedure main() returns () {
  var x : int;
  assume x <= 1000;
  while(x <= 10000000)
  {
      x := 2*x;
  }
  assert x != 10000001;
}



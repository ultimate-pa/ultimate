//#Safe
/*
 * Author: Matthias Heizmann
 * Date: 2015-11-18
 * 
 */

procedure main() returns () {
  var x, y, k : int;
  k := 0;
  assume (y >= k);
  while(*) {
    k := 1;
    y := y + k;
  }
  assert(y >= 0);
}



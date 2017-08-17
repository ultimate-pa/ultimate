//#Unsafe
/* 
 * 
 * 
 * Author: Matthias Heizmann
 * Date: 2017-07-04
 * 
 * 
 */

procedure main() returns () {
  var a : [int]int;
  var i, j : int;
  i := j + 1;
  a[i] := 5;
  a[j] := 7;
  assert(a[i] == 8);
}



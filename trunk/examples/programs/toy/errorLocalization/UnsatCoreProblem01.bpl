//#Unsafe
/* 
 * 
 * Author: Christian Schilling, Matthias Heizmann, Numair Mansur
 * Date: 2017-07-05
 * 
 * 
 */

procedure main() returns () {
  var x, y, z : int;
  assume y==1;
  y := 1; 
  x := 1;
  z := 1;
  assume(x == 1);
  assume(y == 1 || z == 1);
  assert(false);
}



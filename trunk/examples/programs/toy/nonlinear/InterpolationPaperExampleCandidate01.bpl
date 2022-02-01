//#Safe
/*
 * Date: 2015-01-24
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

procedure main() returns ()
{
  var x,y,z: int;
  
  x := y * y + z * z;
  while (*) {
    y := 3;
    z := z + 1;
  }
  assert x != -1;
}

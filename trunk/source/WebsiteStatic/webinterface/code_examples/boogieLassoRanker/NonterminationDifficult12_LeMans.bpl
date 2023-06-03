//#rNonTermination
/*
 * Date: 2015-09-01
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * 
 */

procedure main() returns ()
{
  var x, y, z: real;
  while (x >= y && y >= 1.0) {
     x := 3.0 * x;
     y := 2.0 * y + 100000.0 * z;
	 z := z + 12345678.0;
  }
}


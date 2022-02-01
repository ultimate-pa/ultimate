//#Safe
/*
 * Variant of HiddenEquality.bpl with additional branches.
 * 
 * Date: 2017-03-10
 * Author: heizmann@informatik.uni-freiburg.de and Betim Musa
 *
 */

procedure main()
{
  var x, y, zero, one, hundred: int;
  
  x := 0;
  y := 0;

  while (*) {
	if (x >= 256) {
		x := x - 255;
	} else {
		x := x + 1;
	}
	if (y >= 256) {
		y := y - 255;
	} else {
		y := y + 1;
	}
  }

  assert(x != 100 || y == 100);

} 

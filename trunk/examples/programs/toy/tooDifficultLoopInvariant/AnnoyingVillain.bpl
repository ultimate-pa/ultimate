//#Safe
/*
 * Variation of the HiddenEquality example with modulo operations.
 * The loop invariant (x % 8 == y % 8) allows us to prove correctness.
 * 
 * Date: 2016-12-27
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main()
{
  var x, y: int;
  
  assume x % 256 == 0;
  assume y % 8 == 0;

  while (*) {
    x := x + 1;
    y := y + 1;
  }

  if (x % 256 == 0) {
    assert (y % 8 == 0);
  }
} 

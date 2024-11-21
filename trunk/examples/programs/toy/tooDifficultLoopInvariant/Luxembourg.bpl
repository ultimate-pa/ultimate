//#Safe
/*
 * Variation of the HiddenEquality example.
 * The loop invariant 1000-y>=x allows us to prove correctness.
 * 
 * Date: 2016-04-15
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main()
{
  var x, y: int;
  
  x := 0;
  y := 1000;

  while (*) {
    x := x + 1;
    y := y - 1;
  }

  if (x == 1000) {
    assert (y <= 0);
  }
} 

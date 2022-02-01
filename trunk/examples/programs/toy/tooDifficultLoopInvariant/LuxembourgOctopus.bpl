//#Safe
/*
 * Variation of the Luxembourg example that
 * cannot be solved with the octagon domain.
 * The loop invariant 1000-y<=x allows us to prove correctness.
 * 
 * Date: 2017-02-10
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main()
{
  var x, y, z: int;
  
  x := 0 + z;
  y := 1000;

  while (*) {
    x := x + 1;
    y := y - 1;
  }

  if (x == 1000 + z) {
    assert (y <= 0);
  }
} 

//#Safe
/*
 * Variation of the HiddenEquality example.
 * The loop invariant 1000-y<=x allows us to prove correctness.
 * 
 * Date: 2017-04-26
 * Author: greitsch@informatik.uni-freiburg.de
 *
 */

procedure main()
{
  var x, y: int;
  
  x := 0;
  y := 1000;

  while (*) {
    if (*) {
      x := x + 1;
      y := y - 1;
    } else {
      x := x + 2;
      y := y - 2;
    }
  }

  if (x == 1000) {
    assert (y <= 0);
  }
} 

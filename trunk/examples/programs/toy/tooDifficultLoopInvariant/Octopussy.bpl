//#Safe
/*
 * Simple programs whose correctness cannot be proven directly using
 * the octagon domain.
 * Correctness can be proven using our constraint-based invariant synthesis
 * or using the polyhedra domain.
 * 
 * Date: 2017-03-02
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main()
{
  var x, y: int;
  
  x := 0;
  y := 0;

  while (*) {
    x := x + 1;
    y := y + 2;
  }

  if (x == 1000) {
    assert (y == 2000);
  }
} 

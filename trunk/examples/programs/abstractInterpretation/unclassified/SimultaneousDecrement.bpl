//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Example program, taken from
 * Ranjit Jhala, Kenneth L. McMillan: A Practical and Complete Approach to Predicate Refinement. TACAS 2006
 *
 * The program is correct with respect to the assertions.
 * 
 * In order to prove correctness one has to derive the following invariant.
 * i==j ==> x=y
 */

procedure SimultaneousDecrement()
{
  var x, y, i, j: int;

  x := i;
  y := j;
  while (x!=0) {
    x := x-1;
    y := y-1;
  }
  if (i == j) {
    assert (y == 0);
  }
}
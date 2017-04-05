//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * The program is correct with respect to its specification.
 * But a non-trivial invariant is necessary to prove the
 * correctness.
 * 
 */

procedure StepwiseAddition(x: int, y:int) returns (z: int);
requires x>=0;
requires y>=0;
ensures z == x + y;

implementation StepwiseAddition(x: int, y:int) returns (z:int)
{
  var i, j: int;
  z := 0;
  i := x;
  j := y;
  while(i != 0) {
    z := z + 1;
    i := i - 1;
  }
  while(j != 0) {
    z := z + 1;
    j := j - 1;
  }
}


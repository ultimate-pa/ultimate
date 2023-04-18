//#rNonTerminationDerivable
/*
 * Date: 2013-09-01
 * Author: leike@informatik.uni-freiburg.de
 *
 * A variant of NonTerminationMoreDifficult02.bpl with three variables.
 * x increases, y decreases and z increases,
 * z at a higher rate than y and y at a higher rate than x.
 */

procedure main() returns (x, y, z: real)
{
  while (y + z >= 1.0 && x >= 1.0 && x + y <= 0.0 - 1.0) {
    x := 2.0*x;
    y := 3.0*y;
    z := 7.0*z;
  }
}


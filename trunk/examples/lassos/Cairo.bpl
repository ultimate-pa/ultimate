//#rTermination
/*
 * Ranking function f(x) = x 
 * with supporting invariant x >= 0
 * Makes use of disjunctions in the loop. 
 * Terminates only over the integers not over rationals.
 *
 * Date: 06.04.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure Cairo() returns (x: int)
{
  assume(x > 0);
  while (x != 0) {
    x := x - 1;
  }
}

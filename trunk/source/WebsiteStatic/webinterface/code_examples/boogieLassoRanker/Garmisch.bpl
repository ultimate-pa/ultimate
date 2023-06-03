//#rTermination
/*
 * Date: 2013-01-08
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(x, c) = x - c;
 * needs the supporting invariant c >= -100 for the lower bound,
 * but this supporting invariant is not non-decreasing.
 * 
 * 
 * 
 * Counterexample to the following conjecture. 
 * (Over the integers we are relative complete to Bradley, Manna, Sipma)
 * Over the integers the or2plus template will find each ranking function that
 * the classical linear template finds (i,e., no non-decreasing supporting
 * invariant is required).
 */

procedure Garmisch() returns (x: int)
{
  var c: int;
  assume(c >= 0);
  while (x >= c) {
    x := x - 1;
    havoc c;
    assume(c >= -100);
  }
}
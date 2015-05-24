//#rTermination
/*
 * Date: 2015-05-24
 * Author: heizmann@informatik.uni-freiburg.de
 * Shows that in r14358 RewriteArrays produces only an overapproximation of the
 * Lasso (and is hence not sound for nontermination analysis).
 * In order to be sound, we need the inVar x of the stem to be an index
 * in the loop that gets its own cell variable.
 * Solution: Introduce auxiliary variable (here: for inVar x).
 * Problem: What is the definition of this variable (here: y-1 or x-1)
 */
var a : [int] int;
var k, x, y : int;


procedure main() returns ()
modifies a, k, x, y;
{
  a[x] := 1;
  x := x + 1;
  y := x;
  while (k > 0) {
    k := k - a[y - 1];
  }
}


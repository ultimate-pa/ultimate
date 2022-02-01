//#rTerminationDerivable
/*
 * In 11865 LassoRanker said "Nonterminating" because it was unable to match
 * the replacement cell variable a[k] that stem and loop have in common.
 * Date: 2014-06-26
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var a : [int] int;
var x,k : int;

procedure main() returns ()
modifies a, x;
{
  assume a[k] >= 1;
  while (x >= 0) {
    x := x - a[k];
  }
}


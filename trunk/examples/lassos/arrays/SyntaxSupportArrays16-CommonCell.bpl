//#rTermination
/*
 * In r11832 LassoRanker says "Nonterminating". Problem:
 * Stem and Loop are preprocessed indepentently and we cannot infer that
 * the replacement variable for array cell a[0] is equivalent to the 
 * replacement array cell a[1 - 1]
 * Date: 2014-06-24
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var a : [int] int;
var x,k : int;

procedure main() returns ()
modifies a, x;
{
  assume a[1 - 1] >= 1;
  while (x >= 0) {
    x := x - a[0];
  }
}


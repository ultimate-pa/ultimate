//#rNonTermination
/*
 * Date: 2014-01-07
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Nonterminating program whose executions rotate around (0,0), but the stem
 * excludes (0,0)
 */

var x,y:int;

procedure main() returns ()
modifies x,y;
{
  assume(x >= 1);
  while (true) {
    x := -y;
    y := x;
  }
}

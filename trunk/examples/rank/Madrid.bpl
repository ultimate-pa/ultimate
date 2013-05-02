//#rNontermination
/*
 * Date: 02.05.2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Bug in r8689. Lasso ranker says:
 * Found linear ranking function 0 with linear supporting invariant 0 + 1 * x + -2 >= 0
 */
var x:int;

procedure main() returns ()
modifies x;
{
  while (true) {
    x := 2;
  }
}

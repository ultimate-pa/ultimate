//#rNonTermination
/*
 * Date: 2015-03-13
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Program whose nontermination cannot be proven by the 
 * current version (2015-03-13) of LassoRanker.
 */
var a,b: bool;

procedure proc() returns ()
modifies a,b;
{
  a := true;
  b := false;
  while (*) {
    a,b := b,a;
  }
}

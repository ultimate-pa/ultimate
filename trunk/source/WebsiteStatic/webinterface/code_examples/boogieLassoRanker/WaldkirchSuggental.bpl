//#rNonTermination
/*
 * Bug in r15151. We are unable to find a geometric nontermination argument.
 * Works if we replace > by >=.
 * Works if we use integers (then a predecessor will replace > by >=)
 * Works if we add an update such that there is no fixpoint any more.
 * Date: 2015-09-01
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * 
 */

procedure main() returns ()
{
  var y: real;
  while (y > 1.0) {
  }
}


//#rTerminationDerivable
/*
 * Example that reveals minor bug in our nontermination analysis. We have to
 * transform each constraint into homogenized form.
 * 
 * Discussion with Jan showed that this is no bug. Out method will not find a
 * nontermination argument.
 * 
 * Date: 26.01.2014
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(x,y) = a + -b + 200
 *
 */

procedure main() returns ()
{
var a, b, c : int;
  assume (true);
  while (a >= 0 && b <= 200) {
    a := a + b - 2;
    havoc c;
    assume c >= 0;
    b := 2*b - 1 + c;
  }
}


//#rTerminationDerivable
/*
 * Example that reveales minor bug in our nontermination analysis. We hae to
 * transform each constraint into homogenized form.
 * 
 * Date: 26.01.2014
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(x,y) = x + -y + 200
 *
 */

procedure main() returns ()
{
  var x, y: int;
  assume (true);
  while (x >= 0 && y <= 200) {
    x := x + y - 2;
    y := 2*y - 1;
  }
}


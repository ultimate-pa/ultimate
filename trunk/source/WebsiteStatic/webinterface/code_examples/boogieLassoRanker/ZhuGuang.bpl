//#rTerminationUnknown
/*
 * Date: 2014-12-12
 * Author: Zhu Guang <z975@sina.cn>
 * 
 * Has a nontermination argument
 * LassoRanker fails to extract that argument
 * because it contains nonrational algebraic numbers.
 */

procedure main() returns ()
{
  var x, y, x_old: real;
  while (2.0*x + y>=1.0) {
    x_old := x;
    x := 0.0 - x_old -7.0*y; 
    y := 0.0 - 3.0*x_old;
  }
}


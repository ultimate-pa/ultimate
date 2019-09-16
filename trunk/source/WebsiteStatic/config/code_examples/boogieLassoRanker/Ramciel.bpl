//#rTerminationDerivable
/*
 * Date: 22.04.2012
 * Author: heizmann@informatik.uni-freiburg.de
 * If we require f(v')>=0 this program does not have a linear ranking function.
 * If we only require that f(v)>=0 holds, f(x)=x is a ranking function.
 *
 */

procedure Ramciel() returns ()
{
  var x: int;

  while (x >= 1) {
     x := -x;
  }
}


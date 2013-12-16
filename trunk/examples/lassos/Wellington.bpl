//#rTerminationDerivable
/*
 * Ranking function f(x,y,z) = x
 * 
 * Ranking function not found in revision r5585, because of auxilliary
 * variables which are neither outVars nor inVars
 * 
 * Date: 06.04.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure Wellington() returns ()
{
  var x,y,z: int;

  assume y > 0;
  while (x >= 0) {
    havoc z;
    y := z;
    assume z > 0;
    x := x - y;
  }
}


//#Safe
/* Requires template of six inequalities, but
 * VP domain will easily find invariant.
 * 
 * Date: 2018-08-17
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * 
 */

var x,y,z : int;

procedure main() returns ()
modifies x,y,z;
{
  
  assume(x == 1 && y == 2 && z == 3);
  while (*) {}
  assert(x == 1 && y == 2 && z == 3);
}


